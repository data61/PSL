(*
  File:    Linear_Inhomogenous_Recurrences.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Inhomogenous linear recurrences\<close>
theory Linear_Inhomogenous_Recurrences
imports 
  Complex_Main
  Linear_Homogenous_Recurrences
  Eulerian_Polynomials 
  RatFPS
begin

definition lir_fps_numerator where
  "lir_fps_numerator m cs f g = (let N = length cs - 1 in 
      Poly [(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) - g k. k \<leftarrow> [0..<N+m]])"

lemma lir_fps_numerator_code [code abstract]:
  "coeffs (lir_fps_numerator m cs f g) = (let N = length cs - 1 in 
     strip_while ((=) 0) [(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) - g k. k \<leftarrow> [0..<N+m]])"
  by (simp add: lir_fps_numerator_def Let_def)


locale linear_inhomogenous_recurrence =
  fixes f g :: "nat \<Rightarrow> 'a :: comm_ring" and cs fs :: "'a list"
  assumes base: "n < length fs \<Longrightarrow> f n = fs ! n"
  assumes cs_not_null [simp]: "cs \<noteq> []" and last_cs [simp]: "last cs \<noteq> 0"
      and hd_cs [simp]: "hd cs \<noteq> 0" and enough_base: "length fs + 1 \<ge> length cs"
  assumes rec:  "n \<ge> length fs + 1 - length cs \<Longrightarrow> 
                     (\<Sum>k<length cs. cs ! k * f (n + k)) = g (n + length cs - 1)"
begin

lemma coeff_0_lr_fps_denominator [simp]: "coeff (lr_fps_denominator cs) 0 = last cs"
  by (auto simp: lr_fps_denominator_def nth_default_def nth_Cons hd_conv_nth [symmetric] hd_rev)

lemma lir_fps_numerator_altdef:
  "lir_fps_numerator (length fs + 1 - length cs) cs f g =
     lir_fps_numerator (length fs + 1 - length cs) cs ((!) fs) g"
proof -
  define N where "N = length cs - 1"
  define m where "m = length fs + 1 - length cs"
  have "lir_fps_numerator m cs f g = 
          Poly (map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) - g k) [0..<N + m])"
    by (simp add: lir_fps_numerator_def Let_def N_def)
  also from enough_base have "N + m = length fs"
    by (cases cs) (simp_all add: N_def m_def algebra_simps)
  also {
    fix k assume k: "k \<in> {0..<length fs}"
    hence "f (k - i) = fs ! (k - i)" if "i \<le> min N k" for i 
      using enough_base that by (intro base) (auto simp: Suc_le_eq N_def m_def algebra_simps)
    hence "(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) = (\<Sum>i\<le>min N k. cs ! (N - i) * fs ! (k - i))"
      by simp
  }
  hence "map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) - g k) [0..<length fs] =
           map (\<lambda>k. (\<Sum>i\<le>min N k. cs ! (N - i) * fs ! (k - i)) - g k) [0..<length fs]"
    by (intro map_cong) simp_all
  also have "Poly \<dots> = lir_fps_numerator m cs ((!) fs) g" using enough_base
    by (cases cs) (simp_all add: lir_fps_numerator_def Let_def m_def N_def)
  finally show ?thesis unfolding m_def .
qed

end


context
begin

private lemma lir_fps_aux:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes rec: "\<And>n. n \<ge> m \<Longrightarrow> (\<Sum>k\<le>N. c k * f (n + k)) = g (n + N)"
  assumes cN: "c N \<noteq> 0"
  defines "p \<equiv> Poly [c (N - k). k \<leftarrow> [0..<Suc N]]"
  defines "q \<equiv> Poly [(\<Sum>i\<le>min N k. c (N - i) * f (k - i)) - g k. k \<leftarrow> [0..<N+m]]"
  shows   "Abs_fps f = (fps_of_poly q + Abs_fps g) / fps_of_poly p"
proof -
  include fps_notation
  define F where "F = Abs_fps f"
  have [simp]: "F $ n = f n" for n by (simp add: F_def)
  have [simp]: "coeff p 0 = c N" 
    by (simp add: p_def nth_default_def del: upt_Suc)
  
  have "(fps_of_poly p * F) $ n = coeff q n + g n" for n
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
    also from True have "\<dots> = g (n - N + N)" by (intro rec) simp_all
    also from True have "\<dots> = coeff q n + g n" 
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
    also from False have "\<dots> = coeff q n + g n" by (simp add: q_def nth_default_def)
    finally show ?thesis .
  qed
  hence "fps_of_poly p * F = fps_of_poly q + Abs_fps g" 
    by (intro fps_ext) (simp add:)
  with cN show "F = (fps_of_poly q + Abs_fps g) / fps_of_poly p"
    by (subst unit_eq_div2) (simp_all add: mult_ac)
qed

lemma lir_fps:
  fixes f g :: "nat \<Rightarrow> 'a :: field" and cs :: "'a list"
  defines "N \<equiv> length cs - 1"
  assumes cs: "cs \<noteq> []"
  assumes "\<And>n. n \<ge> m \<Longrightarrow> (\<Sum>k\<le>N. cs ! k * f (n + k)) = g (n + N)"
  assumes cN: "last cs \<noteq> 0"
  shows   "Abs_fps f = (fps_of_poly (lir_fps_numerator m cs f g) + Abs_fps g) / 
              fps_of_poly (lr_fps_denominator cs)"
proof -
  define p and q 
    where "p = Poly [(\<Sum>i\<le>min N k. cs ! (N - i) * f (k - i)) - g k. k \<leftarrow> [0..<N+m]]"
      and "q = Poly (map (\<lambda>k. cs ! (N - k)) [0..<Suc N])"
  from assms have "Abs_fps f = (fps_of_poly p + Abs_fps g) / fps_of_poly q" 
    unfolding p_def q_def by (intro lir_fps_aux) (simp_all add: last_conv_nth)
  also have "p = lir_fps_numerator m cs f g"
    unfolding p_def lir_fps_numerator_def by (auto simp: Let_def N_def)
  also from cN have "q = lr_fps_denominator cs"
    unfolding q_def lr_fps_denominator_def
    by (intro poly_eqI)
       (auto simp add: nth_default_def rev_nth N_def not_less cs simp del: upt_Suc)
  finally show ?thesis .
qed

end


type_synonym 'a polyexp = "('a \<times> nat \<times> 'a) list"

definition eval_polyexp :: "('a::semiring_1) polyexp \<Rightarrow> nat \<Rightarrow> 'a" where
  "eval_polyexp xs = (\<lambda>n. \<Sum>(a,k,b)\<leftarrow>xs. a * of_nat n ^ k * b ^ n)"

lemma eval_polyexp_Nil [simp]: "eval_polyexp [] = (\<lambda>_. 0)"
  by (simp add: eval_polyexp_def)

lemma eval_polyexp_Cons: 
  "eval_polyexp (x#xs) = (\<lambda>n. (case x of (a,k,b) \<Rightarrow> a * of_nat n ^ k * b ^ n) + eval_polyexp xs n)"
  by (simp add: eval_polyexp_def)

  
definition polyexp_fps :: "('a :: field) polyexp \<Rightarrow> 'a fps" where
  "polyexp_fps xs = 
     (\<Sum>(a,k,b)\<leftarrow>xs. fps_of_poly (Polynomial.smult a (fps_monom_poly b k)) / 
                       (1 - fps_const b * fps_X) ^ (k + 1))"

lemma polyexp_fps_Nil [simp]: "polyexp_fps [] = 0"
  by (simp add: polyexp_fps_def)

lemma polyexp_fps_Cons: 
  "polyexp_fps (x#xs) = (case x of (a,k,b) \<Rightarrow> 
     fps_of_poly (Polynomial.smult a (fps_monom_poly b k)) / (1 - fps_const b * fps_X) ^ (k + 1)) + 
     polyexp_fps xs"
  by (simp add: polyexp_fps_def)

definition polyexp_ratfps :: "('a :: {field,factorial_ring_gcd}) polyexp \<Rightarrow> 'a ratfps" where
  "polyexp_ratfps xs = 
     (\<Sum>(a,k,b)\<leftarrow>xs. ratfps_of_poly (Polynomial.smult a (fps_monom_poly b k)) /
                       ratfps_of_poly ([:1, -b:] ^ (k + 1)))"
     
lemma polyexp_ratfps_Nil [simp]: "polyexp_ratfps [] = 0"
  by (simp add: polyexp_ratfps_def)

lemma polyexp_ratfps_Cons: "polyexp_ratfps (x#xs) = (case x of (a,k,b) \<Rightarrow>
  ratfps_of_poly (Polynomial.smult a (fps_monom_poly b k)) / 
     ratfps_of_poly ([:1, -b:] ^ (k + 1))) + polyexp_ratfps xs"
  by (simp add: polyexp_ratfps_def)

lemma polyexp_fps: "Abs_fps (eval_polyexp xs) = polyexp_fps xs"
proof (induction xs)
  case (Cons x xs)
  obtain a k b where [simp]: "x = (a, k, b)" by (metis prod.exhaust)
  have "Abs_fps (eval_polyexp (x#xs)) = 
          fps_const a * Abs_fps (\<lambda>n. of_nat n ^ k * b ^ n) + Abs_fps (eval_polyexp xs)"
    by (simp add: eval_polyexp_Cons fps_plus_def mult_ac)
  also have "Abs_fps (\<lambda>n. of_nat n ^ k * b ^ n) = 
               fps_of_poly (fps_monom_poly b k) / (1 - fps_const b * fps_X) ^ (k + 1)" 
            (is "_ = ?A / ?B")
    by (rule fps_monom)
  also have "fps_const a * (?A / ?B) = (fps_const a * ?A) / ?B"
    by (intro unit_div_mult_swap) simp_all
  also have "fps_const a * ?A = fps_of_poly (Polynomial.smult a (fps_monom_poly b k))"
    by simp
  also note Cons.IH
  finally show ?case by (simp add: polyexp_fps_Cons)
qed (simp_all add: fps_zero_def)

lemma polyexp_ratfps [simp]: "fps_of_ratfps (polyexp_ratfps xs) = polyexp_fps xs"
  by (induction xs)
     (auto simp del: power_Suc fps_const_neg 
           simp: coeff_0_power fps_of_poly_power fps_of_poly_smult fps_of_poly_pCons 
                 fps_const_neg [symmetric] mult_ac polyexp_ratfps_Cons polyexp_fps_Cons)


definition lir_fps :: 
    "'a :: {field,factorial_ring_gcd} list \<Rightarrow> 'a list \<Rightarrow> 'a polyexp \<Rightarrow> ('a ratfps) option" where
  "lir_fps cs fs g = (if cs = [] \<or> length fs < length cs - 1 then None else
     let m = length fs + 1 - length cs;
         p = lir_fps_numerator m cs (\<lambda>n. fs ! n) (eval_polyexp g);
         q = lr_fps_denominator cs
     in  Some ((ratfps_of_poly p + polyexp_ratfps g) * inverse (ratfps_of_poly q)))"

lemma lir_fps_correct:
  fixes   f :: "nat \<Rightarrow> 'a :: {field,factorial_ring_gcd}"
  assumes "linear_inhomogenous_recurrence f (eval_polyexp g) cs fs"
  shows   "map_option fps_of_ratfps (lir_fps cs fs g) = Some (Abs_fps f)"
proof -
  interpret linear_inhomogenous_recurrence f "eval_polyexp g" cs fs by fact
  define m where "m = length fs + 1 - length cs"
  let ?num = "lir_fps_numerator m cs f (eval_polyexp g)"
  let ?num' = "lir_fps_numerator m cs ((!) fs) (eval_polyexp g)"
  let ?denom = "lr_fps_denominator cs"
 
  have "{..length cs - 1} = {..<length cs}" by (cases cs) auto
  moreover have "length cs \<ge> 1" by (cases cs) auto
  ultimately have "Abs_fps f = (fps_of_poly ?num + Abs_fps (eval_polyexp g)) / fps_of_poly ?denom"
    by (intro lir_fps) (insert rec, simp_all add: m_def)
  also have "?num = ?num'" by (rule lir_fps_numerator_altdef [folded m_def])
  also have "(fps_of_poly ?num' + Abs_fps (eval_polyexp g)) / fps_of_poly ?denom = 
                fps_of_ratfps ((ratfps_of_poly ?num' + polyexp_ratfps g) * 
                  inverse (ratfps_of_poly ?denom))"
    by (simp add: polyexp_fps fps_divide_unit)
  also from enough_base have "Some \<dots> = map_option fps_of_ratfps (lir_fps cs fs g)"
    by (cases cs) (simp_all add: base fps_of_ratfps_def case_prod_unfold lir_fps_def m_def)
  finally show ?thesis ..
qed

end
