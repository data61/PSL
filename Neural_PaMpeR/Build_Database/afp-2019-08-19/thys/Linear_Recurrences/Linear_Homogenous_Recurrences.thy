(*
  File:    Linear_Homogenous_Recurrences.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Homogenous linear recurrences\<close>
theory Linear_Homogenous_Recurrences
imports 
  Complex_Main
  RatFPS
  Rational_FPS_Solver
  Linear_Recurrences_Common
begin

text \<open>
  The following is the numerator of the rational generating function of a 
  linear homogenous recurrence.
\<close>
definition lhr_fps_numerator where
  "lhr_fps_numerator m cs f = (let N = length cs - 1 in 
      Poly [(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)). k \<leftarrow> [0..<N+m]])"
      
lemma lhr_fps_numerator_code [code abstract]:
  "coeffs (lhr_fps_numerator m cs f) = (let N = length cs - 1 in 
     strip_while ((=) 0) [(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)). k \<leftarrow> [0..<N+m]])"
  by (simp add: lhr_fps_numerator_def Let_def)
 
lemma lhr_fps_aux:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "\<And>n. n \<ge> m \<Longrightarrow> (\<Sum>k\<le>N. c k * f (n + k)) = 0"
  assumes cN: "c N \<noteq> 0"
  defines "p \<equiv> Poly [c (N - k). k \<leftarrow> [0..<Suc N]]"
  defines "q \<equiv> Poly [(\<Sum>i\<le>min N k. c (N - i) * f (k - i)). k \<leftarrow> [0..<N+m]]"
  shows   "Abs_fps f = fps_of_poly q / fps_of_poly p"
proof -
  include fps_notation
  define F where "F = Abs_fps f"
  have [simp]: "F $ n = f n" for n by (simp add: F_def)
  have [simp]: "coeff p 0 = c N" 
    by (simp add: p_def nth_default_def del: upt_Suc)
  
  have "(fps_of_poly p * F) $ n = coeff q n" for n
  proof (cases "n \<ge> N + m")
    case True
    let ?f = "\<lambda>i. N - i"
    have "(fps_of_poly p * F) $ n = (\<Sum>i\<le>n. coeff p i * f (n - i))"
      by (simp add: fps_mult_nth atLeast0AtMost)
    also from True have "\<dots> = (\<Sum>i\<le>N. coeff p i * f (n - i))"
      by (intro sum.mono_neutral_right) (auto simp: nth_default_def p_def)
    also have "\<dots> = (\<Sum>i\<le>N. c (N - i) * f (n - i))" 
      by (intro sum.cong) (auto simp: nth_default_def p_def simp del: upt_Suc)
    also from True have "\<dots> = (\<Sum>i\<le>N. c i * f (n - N + i))"
      by (intro sum.reindex_bij_witness[of _ ?f ?f]) auto
    also from True have "\<dots> = 0" by (intro assms) simp_all
    also from True have "\<dots> = coeff q n" 
      by (simp add: q_def nth_default_def del: upt_Suc)
    finally show ?thesis .
  next
    case False
    hence "(fps_of_poly p * F) $ n = (\<Sum>i\<le>n. coeff p i * f (n - i))"
      by (simp add: fps_mult_nth atLeast0AtMost)
    also have "\<dots> = (\<Sum>i\<le>min N n. coeff p i * f (n - i))"
      by (intro sum.mono_neutral_right)
         (auto simp: p_def nth_default_def simp del: upt_Suc)
    also have "\<dots> = (\<Sum>i\<le>min N n. c (N - i) * f (n - i))"
      by (intro sum.cong) (simp_all add: p_def nth_default_def del: upt_Suc)
    also from False have "\<dots> = coeff q n" by (simp add: q_def nth_default_def)
    finally show ?thesis .
  qed
  hence "fps_of_poly p * F = fps_of_poly q" 
    by (intro fps_ext) simp
  with cN show "F = fps_of_poly q / fps_of_poly p"
    by (subst unit_eq_div2) (simp_all add: mult_ac)
qed

lemma lhr_fps:
  fixes f :: "nat \<Rightarrow> 'a :: field" and cs :: "'a list"
  defines "N \<equiv> length cs - 1"
  assumes cs: "cs \<noteq> []"
  assumes "\<And>n. n \<ge> m \<Longrightarrow> (\<Sum>k\<le>N. cs ! k * f (n + k)) = 0"
  assumes cN: "last cs \<noteq> 0"
  shows   "Abs_fps f = fps_of_poly (lhr_fps_numerator m cs f) / 
              fps_of_poly (lr_fps_denominator cs)"
proof -
  define p and q 
    where "p = Poly (map (\<lambda>k. \<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) [0..<N + m])"
      and "q = Poly (map (\<lambda>k. cs ! (N - k)) [0..<Suc N])"

  from assms have "Abs_fps f = fps_of_poly p / fps_of_poly q" unfolding p_def q_def
    by (intro lhr_fps_aux) (simp_all add: last_conv_nth)
  also have "p = lhr_fps_numerator m cs f"
    unfolding p_def lhr_fps_numerator_def by (auto simp: Let_def N_def)
  also from cN have "q = lr_fps_denominator cs"
    unfolding q_def lr_fps_denominator_def
    by (intro poly_eqI)
       (auto simp add: nth_default_def rev_nth N_def not_less cs simp del: upt_Suc)
  finally show ?thesis .
qed

(* TODO: Do I even need this? *)
fun lhr where
  "lhr cs fs n =
     (if (cs :: 'a :: field list) = [] \<or> last cs = 0 \<or> length fs < length cs - 1 then undefined else
     (if n < length fs then fs ! n else 
          (\<Sum>k<length cs - 1. cs ! k * lhr cs fs (n + 1 - length cs + k)) / -last cs))"

declare lhr.simps [simp del]

lemma lhr_rec: 
  assumes "cs \<noteq> []" "last cs \<noteq> 0" "length fs \<ge> length cs - 1" "n \<ge> length fs"
  shows   "(\<Sum>k<length cs. cs ! k * lhr cs fs (n + 1 - length cs + k)) = 0"
proof -
  from assms have "{..<length cs} = insert (length cs - 1) {..<length cs - 1}" by auto
  also have "(\<Sum>k\<in>\<dots> . cs ! k * lhr cs fs (n + 1 - length cs + k)) =
               (\<Sum>k<length cs - 1. cs ! k * lhr cs fs (n + 1 - length cs + k)) + 
                    last cs * lhr cs fs n" using assms
    by (cases cs) (simp_all add: algebra_simps last_conv_nth)
  also from assms have "\<dots> = 0" by (subst (2) lhr.simps) (simp_all add: field_simps)
  finally show ?thesis .
qed

lemma lhrI:
  assumes "cs \<noteq> []" "last cs \<noteq> 0" "length fs \<ge> length cs - 1"
  assumes "\<And>n. n < length fs \<Longrightarrow> f n = fs ! n"
  assumes "\<And>n. n \<ge> length fs \<Longrightarrow> (\<Sum>k<length cs. cs ! k * f (n + 1 - length cs + k)) = 0"
  shows   "f n = lhr cs fs n"
using assms
proof (induction cs fs n rule: lhr.induct)
  case (1 cs fs n)
  show ?case
  proof (cases "n < length fs")
    case False
    with 1 have "0 = (\<Sum>k<length cs. cs ! k * f (n + 1 - length cs + k))" by simp
    also from 1 have "{..<length cs} = insert (length cs - 1) {..<length cs - 1}" by auto
    also have "(\<Sum>k\<in>\<dots> . cs ! k * f (n + 1 - length cs + k)) =
                 (\<Sum>k<length cs - 1. cs ! k * f (n + 1 - length cs + k)) + 
                      last cs * f n" using 1 False
      by (cases cs) (simp_all add: algebra_simps last_conv_nth)
    also have "(\<Sum>k<length cs - 1. cs ! k * f (n + 1 - length cs + k)) =
                   (\<Sum>k<length cs - 1. cs ! k * lhr cs fs (n + 1 - length cs + k))"
      using False 1 by (intro sum.cong refl) simp
    finally have "f n = (\<Sum>k<length cs - 1. cs ! k * lhr cs fs (n + 1 - length cs + k)) / -last cs"
      using \<open>last cs \<noteq> 0\<close> by (simp add: field_simps eq_neg_iff_add_eq_0)
  also from 1(2-4) False have "\<dots> = lhr cs fs n" by (subst lhr.simps) simp
    finally show ?thesis .
  qed (insert 1(2-5), simp add: lhr.simps)
qed
(* END TODO *)

locale linear_homogenous_recurrence =
  fixes f :: "nat \<Rightarrow> 'a :: comm_semiring_0" and cs fs :: "'a list"
  assumes base: "n < length fs \<Longrightarrow> f n = fs ! n"
  assumes cs_not_null [simp]: "cs \<noteq> []" and last_cs [simp]: "last cs \<noteq> 0"
      and hd_cs [simp]: "hd cs \<noteq> 0" and enough_base: "length fs + 1 \<ge> length cs"
  assumes rec:  "n \<ge> length fs - length cs \<Longrightarrow> (\<Sum>k<length cs. cs ! k * f (n + k)) = 0"
begin

lemma lhr_fps_numerator_altdef:
  "lhr_fps_numerator (length fs + 1 - length cs) cs f =
     lhr_fps_numerator (length fs + 1 - length cs) cs ((!) fs)"
proof -
  define N where "N = length cs - 1"
  define m where "m = length fs + 1 - length cs"
  have "lhr_fps_numerator m cs f = 
          Poly (map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i))) [0..<N + m])"
    by (simp add: lhr_fps_numerator_def Let_def N_def)
  also from enough_base have "N + m = length fs"
    by (cases cs) (simp_all add: N_def m_def algebra_simps)
  also {
    fix k assume k: "k \<in> {0..<length fs}"
    hence "f (k - i) = fs ! (k - i)" if "i \<le> min N k" for i 
      using enough_base that by (intro base) (auto simp: Suc_le_eq N_def m_def algebra_simps)
    hence "(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) = (\<Sum>i\<le>min N k. cs ! (N - i) * fs ! (k - i))"
      by simp
  }
  hence "map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i))) [0..<length fs] =
           map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * fs ! (k - i))) [0..<length fs]"
    by (intro map_cong) simp_all
  also have "Poly \<dots> = lhr_fps_numerator m cs ((!) fs)" using enough_base
    by (cases cs) (simp_all add: lhr_fps_numerator_def Let_def m_def N_def)
  finally show ?thesis unfolding m_def .
qed

end

(* TODO Duplication *)
lemma solve_lhr_aux:
  assumes "linear_homogenous_recurrence f cs fs"
  assumes "is_factorization_of fctrs (lr_fps_denominator' cs)"
  shows   "f = interp_ratfps_solution (solve_factored_ratfps' (lhr_fps_numerator 
                  (length fs + 1 - length cs) cs ((!) fs)) fctrs)"
proof -
  interpret linear_homogenous_recurrence f cs fs by fact

  note assms(2)
  hence "is_alt_factorization_of fctrs (reflect_poly (lr_fps_denominator' cs))"
    by (intro reflect_factorization) 
       (simp_all add: lr_fps_denominator'_def
                      nth_default_def hd_conv_nth [symmetric])
  also have "reflect_poly (lr_fps_denominator' cs) = lr_fps_denominator cs"
    unfolding lr_fps_denominator_def lr_fps_denominator'_def
    by (subst coeffs_eq_iff) (simp add: coeffs_reflect_poly strip_while_rev [symmetric]
                                 no_trailing_unfold last_rev del: strip_while_rev)
  finally have factorization: "is_alt_factorization_of fctrs (lr_fps_denominator cs)" .

  define m where "m = length fs + 1 - length cs"
  obtain a ds where fctrs: "fctrs = (a, ds)" by (cases fctrs) simp_all
  define p and p' where "p = lhr_fps_numerator m cs ((!) fs)" and "p' = smult (inverse a) p"
  obtain b es where sol: "solve_factored_ratfps' p fctrs = (b, es)" 
    by (cases "solve_factored_ratfps' p fctrs") simp_all
  have sol': "(b, es) = solve_factored_ratfps p' ds"
    by (subst sol [symmetric]) (simp add: fctrs p'_def solve_factored_ratfps_def 
                                          solve_factored_ratfps'_def case_prod_unfold)
  have factorization': "lr_fps_denominator cs = interp_alt_factorization fctrs"
    using factorization by (simp add: is_alt_factorization_of_def)
  from assms(2) have distinct: "distinct (map fst ds)"
    by (simp add: fctrs is_factorization_of_def)
  have coeff_0_denom: "coeff (lr_fps_denominator cs) 0 \<noteq> 0" 
    by (simp add: lr_fps_denominator_def nth_default_def 
                  hd_conv_nth [symmetric] hd_rev)
  have "coeff (lr_fps_denominator' cs) 0 \<noteq> 0"
    by (simp add: lr_fps_denominator'_def nth_default_def hd_conv_nth [symmetric])
  with assms(2) have no_zero: "0 \<notin> fst ` set ds" by (simp add: zero_in_factorization_iff fctrs)
    
  from assms(2) have a_nz [simp]: "a \<noteq> 0"
    by (auto simp: fctrs interp_factorization_def is_factorization_of_def lr_fps_denominator'_nz)
  hence unit1: "is_unit (fps_const a)" by simp
  moreover have "is_unit (fps_of_poly (interp_alt_factorization fctrs))"
    by (simp add: coeff_0_denom factorization' [symmetric])
  ultimately have unit2: "is_unit (fps_of_poly (\<Prod>p\<leftarrow>ds. [:1, - fst p:] ^ Suc (snd p)))"
    by (simp add: fctrs case_prod_unfold interp_alt_factorization_def del: power_Suc)
  
  have "Abs_fps f = fps_of_poly (lhr_fps_numerator m cs f) /
                        fps_of_poly (lr_fps_denominator cs)"
  proof (intro lhr_fps)
    fix n assume n: "n \<ge> m"
    have "{..length cs - 1} = {..<length cs}" by (cases cs) auto
    also from n have "(\<Sum>k\<in>\<dots> . cs ! k * f (n + k)) = 0"
      by (intro rec) (simp_all add: m_def algebra_simps)
    finally show "(\<Sum>k\<le>length cs - 1. cs ! k * f (n + k)) = 0" .
  qed (simp_all add: m_def)
  also have "lhr_fps_numerator m cs f = lhr_fps_numerator m cs ((!) fs)"
    unfolding lhr_fps_numerator_def using enough_base
    by (auto simp: Let_def poly_eq_iff nth_default_def base 
                   m_def Suc_le_eq intro!: sum.cong)
  also have "fps_of_poly \<dots> / fps_of_poly (lr_fps_denominator cs) = 
               fps_of_poly (lhr_fps_numerator m cs ((!) fs)) / 
                 (fps_const (fst fctrs) * 
                   fps_of_poly (\<Prod>p\<leftarrow>snd fctrs. [:1, - fst p:] ^ Suc (snd p)))"
    unfolding assms factorization' interp_alt_factorization_def
    by (simp add: case_prod_unfold Let_def fps_of_poly_smult)
  also from unit1 unit2 have "\<dots> = fps_of_poly p / fps_const a / 
                                     fps_of_poly (\<Prod>(c,n)\<leftarrow>ds. [:1, -c:]^Suc n)"
    by (subst is_unit_div_mult2_eq) (simp_all add: fctrs case_prod_unfold p_def)
  also from unit1 have "fps_of_poly p / fps_const a = fps_of_poly p'"
    by (simp add: fps_divide_unit fps_of_poly_smult fps_const_inverse p'_def)
  also from distinct no_zero have "\<dots> / fps_of_poly (\<Prod>(c,n)\<leftarrow>ds. [:1, -c:]^Suc n) = 
      Abs_fps (interp_ratfps_solution (solve_factored_ratfps' p fctrs))"
    by (subst solve_factored_ratfps) (simp_all add: case_prod_unfold sol' sol)
  finally show ?thesis unfolding p_def m_def
    by (intro ext) (simp add: fps_eq_iff)
qed

definition
  "lhr_fps as fs = (
     let m = length fs + 1 - length as;
         p = lhr_fps_numerator m as (\<lambda>n. fs ! n);
         q = lr_fps_denominator as
     in  ratfps_of_poly p / ratfps_of_poly q)"

lemma lhr_fps_correct:
  fixes   f :: "nat \<Rightarrow> 'a :: {field_char_0,factorial_ring_gcd}"
  assumes "linear_homogenous_recurrence f cs fs"
  shows   "fps_of_ratfps (lhr_fps cs fs) = Abs_fps f"
proof -
  interpret linear_homogenous_recurrence f cs fs by fact
  define m where "m = length fs + 1 - length cs"
  let ?num = "lhr_fps_numerator m cs f"
  let ?num' = "lhr_fps_numerator m cs ((!) fs)"
  let ?denom = "lr_fps_denominator cs"
 
  have "{..length cs - 1} = {..<length cs}" by (cases cs) auto
  moreover have "length cs \<ge> 1" by (cases cs) auto
  ultimately have "Abs_fps f = fps_of_poly ?num / fps_of_poly ?denom"
    by (intro lhr_fps) (insert rec, simp_all add: m_def)
  also have "?num = ?num'"
    by (rule lhr_fps_numerator_altdef [folded m_def])
  also have "fps_of_poly ?num' / fps_of_poly ?denom = 
                fps_of_ratfps (ratfps_of_poly ?num' / ratfps_of_poly ?denom)"
    by simp
  also from enough_base have "\<dots> = fps_of_ratfps (lhr_fps cs fs)"
    by (cases cs)  (simp_all add: base fps_of_ratfps_def case_prod_unfold lhr_fps_def m_def)
  finally show ?thesis .. 
qed

end
