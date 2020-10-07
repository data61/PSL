(*
  File:    RatFPS.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Rational formal power series\<close>
theory RatFPS
imports 
  Complex_Main 
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

subsection \<open>Some auxiliary\<close>

abbreviation constant_term :: "'a poly \<Rightarrow> 'a::zero"
  where "constant_term p \<equiv> coeff p 0"

lemma coeff_0_mult: "coeff (p * q) 0 = coeff p 0 * coeff q 0"
  by (simp add: coeff_mult)

lemma coeff_0_div: 
  assumes "coeff p 0 \<noteq> 0" 
  assumes "(q :: 'a :: field poly) dvd p"
  shows   "coeff (p div q) 0 = coeff p 0 div coeff q 0"
proof (cases "q = 0")
  case False
  from assms have "p = p div q * q" by simp
  also have "coeff \<dots> 0 = coeff (p div q) 0 * coeff q 0" by (simp add: coeff_0_mult)
  finally show ?thesis using assms by auto
qed simp_all

lemma coeff_0_add_fract_nonzero:
  assumes "coeff (snd (quot_of_fract x)) 0 \<noteq> 0" "coeff (snd (quot_of_fract y)) 0 \<noteq> 0"
  shows   "coeff (snd (quot_of_fract (x + y))) 0 \<noteq> 0"
proof -
  define num where "num = fst (quot_of_fract x) * snd (quot_of_fract y) + 
    snd (quot_of_fract x) * fst (quot_of_fract y)"
  define denom where "denom = snd (quot_of_fract x) * snd (quot_of_fract y)"
  define z where "z = (num, denom)"
  from assms have "snd z \<noteq> 0" by (auto simp: denom_def z_def)
  from normalize_quotE'[OF this] guess d . note d = this
  from assms have z: "coeff (snd z) 0 \<noteq> 0" by (simp add: z_def denom_def coeff_0_mult)
  
  have "coeff (snd (quot_of_fract (x + y))) 0 = coeff (snd (normalize_quot z)) 0"
    by (simp add: quot_of_fract_add Let_def case_prod_unfold z_def num_def denom_def)
  also from z have "\<dots> \<noteq> 0" using d by (simp add: d coeff_0_mult)
  finally show ?thesis .
qed

lemma coeff_0_normalize_quot_nonzero [simp]:
  assumes "coeff (snd x) 0 \<noteq> 0"
  shows   "coeff (snd (normalize_quot x)) 0 \<noteq> 0"
proof -
  from assms have "snd x \<noteq> 0" by auto
  from normalize_quotE'[OF this] guess d .
  with assms show ?thesis by (auto simp: coeff_0_mult)
qed

abbreviation numerator :: "'a fract \<Rightarrow> 'a::{ring_gcd,idom_divide}"
  where "numerator x \<equiv> fst (quot_of_fract x)"

abbreviation denominator :: "'a fract \<Rightarrow> 'a::{ring_gcd,idom_divide}"
  where "denominator x \<equiv> snd (quot_of_fract x)"

declare unit_factor_snd_quot_of_fract [simp]
  normalize_snd_quot_of_fract [simp]

lemma constant_term_denominator_nonzero_imp_constant_term_denominator_div_gcd_nonzero:
  "constant_term (denominator x div gcd a (denominator x)) \<noteq> 0"
  if "constant_term (denominator x) \<noteq> 0"
  using that coeff_0_normalize_quot_nonzero [of "(a, denominator x)"]
  normalize_quot_proj(2) [of "denominator x" a]
  by simp


subsection \<open>The type of rational formal power series\<close>

typedef (overloaded) 'a :: "{field,factorial_ring_gcd}" ratfps = 
  "{x :: 'a poly fract. constant_term (denominator x) \<noteq> 0}"
  by (rule exI [of _ 0]) simp

setup_lifting type_definition_ratfps

instantiation ratfps :: ("{field,factorial_ring_gcd}") idom
begin

lift_definition zero_ratfps :: "'a ratfps" is "0" by simp

lift_definition one_ratfps :: "'a ratfps" is "1" by simp

lift_definition uminus_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps" is "uminus" 
  by (simp add: quot_of_fract_uminus case_prod_unfold Let_def)

lift_definition plus_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> 'a ratfps" is "(+)"
  by (rule coeff_0_add_fract_nonzero)

lift_definition minus_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> 'a ratfps" is "(-)"
  by (simp only: diff_conv_add_uminus, rule coeff_0_add_fract_nonzero)
     (simp_all add: quot_of_fract_uminus Let_def case_prod_unfold)

lift_definition times_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> 'a ratfps" is "(*)"
  by (simp add: quot_of_fract_mult Let_def case_prod_unfold coeff_0_mult
    constant_term_denominator_nonzero_imp_constant_term_denominator_div_gcd_nonzero)
 
instance
  by (standard; transfer) (simp_all add: ring_distribs)

end

fun ratfps_nth_aux :: "('a::field) poly \<Rightarrow> nat \<Rightarrow> 'a"
where
  "ratfps_nth_aux p 0 = inverse (coeff p 0)"
| "ratfps_nth_aux p n = 
     - inverse (coeff p 0) * sum (\<lambda>i. coeff p i * ratfps_nth_aux p (n - i)) {1..n}"

lemma ratfps_nth_aux_correct: "ratfps_nth_aux p n = natfun_inverse (fps_of_poly p) n"
  by (induction p n rule: ratfps_nth_aux.induct) simp_all

lift_definition ratfps_nth :: "'a :: {field,factorial_ring_gcd} ratfps \<Rightarrow> nat \<Rightarrow> 'a" is
  "\<lambda>x n. let (a,b) = quot_of_fract x
         in  (\<Sum>i = 0..n. coeff a i * ratfps_nth_aux b (n - i))" .

lift_definition ratfps_subdegree :: "'a :: {field,factorial_ring_gcd} ratfps \<Rightarrow> nat" is
  "\<lambda>x. poly_subdegree (fst (quot_of_fract x))" . 

context
includes lifting_syntax
begin
  
lemma RatFPS_parametric: "(rel_prod (=) (=) ===> (=))
  (\<lambda>(p,q). if coeff q 0 = 0 then 0 else quot_to_fract (p, q))
  (\<lambda>(p,q). if coeff q 0 = 0 then 0 else quot_to_fract (p, q))"
  by transfer_prover
  
end


lemma normalize_quot_quot_of_fract [simp]: 
  "normalize_quot (quot_of_fract x) = quot_of_fract x"
  by (rule normalize_quot_id, rule quot_of_fract_in_normalized_fracts)

context
assumes "SORT_CONSTRAINT('a::{field,factorial_ring_gcd})"
begin

lift_definition quot_of_ratfps :: "'a ratfps \<Rightarrow> ('a poly \<times> 'a poly)" is
  "quot_of_fract :: 'a poly fract \<Rightarrow> ('a poly \<times> 'a poly)" .

lift_definition quot_to_ratfps :: "('a poly \<times> 'a poly) \<Rightarrow> 'a ratfps" is
  "\<lambda>(x,y). let (x',y') = normalize_quot (x,y) 
           in  if coeff y' 0 = 0 then 0 else quot_to_fract (x',y')"
  by (simp add: case_prod_unfold Let_def quot_of_fract_quot_to_fract)

lemma quot_to_ratfps_quot_of_ratfps [code abstype]:
  "quot_to_ratfps (quot_of_ratfps x) = x"
  by transfer (simp add: case_prod_unfold Let_def)

lemma coeff_0_snd_quot_of_ratfps_nonzero [simp]: 
  "coeff (snd (quot_of_ratfps x)) 0 \<noteq> 0"
  by transfer simp

lemma quot_of_ratfps_quot_to_ratfps:
  "coeff (snd x) 0 \<noteq> 0 \<Longrightarrow> x \<in> normalized_fracts \<Longrightarrow> quot_of_ratfps (quot_to_ratfps x) = x"
  by transfer (simp add: Let_def case_prod_unfold coeff_0_normalize_quot_nonzero 
                 quot_of_fract_quot_to_fract normalize_quot_id)

lemma quot_of_ratfps_0 [simp, code abstract]: "quot_of_ratfps 0 = (0, 1)"
  by transfer simp_all

lemma quot_of_ratfps_1 [simp, code abstract]: "quot_of_ratfps 1 = (1, 1)"
  by transfer simp_all

lift_definition ratfps_of_poly :: "'a poly \<Rightarrow> 'a ratfps" is
  "to_fract :: 'a poly \<Rightarrow> _"
  by transfer simp

lemma ratfps_of_poly_code [code abstract]:
  "quot_of_ratfps (ratfps_of_poly p) = (p, 1)"
  by transfer' simp

lemmas zero_ratfps_code = quot_of_ratfps_0

lemmas one_ratfps_code = quot_of_ratfps_1
  
lemma uminus_ratfps_code [code abstract]: 
  "quot_of_ratfps (- x) = (let (a, b) = quot_of_ratfps x in (-a, b))"
  by transfer (rule quot_of_fract_uminus)

lemma plus_ratfps_code [code abstract]:
  "quot_of_ratfps (x + y) = 
     (let (a,b) = quot_of_ratfps x; (c,d) = quot_of_ratfps y
      in  normalize_quot (a * d + b * c, b * d))"
  by transfer' (rule quot_of_fract_add)

lemma minus_ratfps_code [code abstract]:
  "quot_of_ratfps (x - y) = 
     (let (a,b) = quot_of_ratfps x; (c,d) = quot_of_ratfps y
      in  normalize_quot (a * d - b * c, b * d))"
  by transfer' (rule quot_of_fract_diff) 

definition ratfps_cutoff :: "nat \<Rightarrow> 'a :: {field,factorial_ring_gcd} ratfps \<Rightarrow> 'a poly" where
  "ratfps_cutoff n x = poly_of_list (map (ratfps_nth x) [0..<n])"

definition ratfps_shift :: "nat \<Rightarrow> 'a :: {field,factorial_ring_gcd} ratfps \<Rightarrow> 'a ratfps" where
  "ratfps_shift n x = (let (a, b) = quot_of_ratfps (x - ratfps_of_poly (ratfps_cutoff n x))
                       in  quot_to_ratfps (poly_shift n a, b))"
 
lemma times_ratfps_code [code abstract]:
  "quot_of_ratfps (x * y) = 
     (let (a,b) = quot_of_ratfps x; (c,d) = quot_of_ratfps y;
          (e,f) = normalize_quot (a,d); (g,h) = normalize_quot (c,b)
      in  (e*g, f*h))"
  by transfer' (rule quot_of_fract_mult)

lemma ratfps_nth_code [code]:
  "ratfps_nth x n = 
    (let (a,b) = quot_of_ratfps x
     in  \<Sum>i = 0..n. coeff a i * ratfps_nth_aux b (n - i))"
  by transfer' simp

lemma ratfps_subdegree_code [code]:
  "ratfps_subdegree x = poly_subdegree (fst (quot_of_ratfps x))"
  by transfer simp

end

instantiation ratfps :: ("{field,factorial_ring_gcd}") inverse
begin

lift_definition inverse_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps" is
  "\<lambda>x. let (a,b) = quot_of_fract x
       in  if coeff a 0 = 0 then 0 else inverse x"
  by (auto simp: case_prod_unfold Let_def quot_of_fract_inverse)

lift_definition divide_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> 'a ratfps" is
  "\<lambda>f g. (if g = 0 then 0 else 
           let n = ratfps_subdegree g; h = ratfps_shift n g
           in  ratfps_shift n (f * inverse h))" .  

instance ..
end

lemma ratfps_inverse_code [code abstract]:
  "quot_of_ratfps (inverse x) = 
     (let (a,b) = quot_of_ratfps x
      in  if coeff a 0 = 0 then (0, 1)
          else let u = unit_factor a in (b div u, a div u))"
  by transfer' (simp_all add: Let_def case_prod_unfold quot_of_fract_inverse)

instantiation ratfps :: (equal) equal
begin

definition equal_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> bool" where
  [simp]: "equal_ratfps x y \<longleftrightarrow> x = y"

instance by standard simp

end

lemma quot_of_fract_eq_iff [simp]: "quot_of_fract x = quot_of_fract y \<longleftrightarrow> x = y"
  by transfer (auto simp: normalize_quot_eq_iff)

lemma equal_ratfps_code [code]: "HOL.equal x y \<longleftrightarrow> quot_of_ratfps x = quot_of_ratfps y"
  unfolding equal_ratfps_def by transfer simp

lemma fps_of_poly_quot_normalize_quot [simp]:
  "fps_of_poly (fst (normalize_quot x)) / fps_of_poly (snd (normalize_quot x)) =
     fps_of_poly (fst x) / fps_of_poly (snd x)"
  if "(snd x :: 'a :: {field, factorial_ring_gcd} poly) \<noteq> 0"
proof -
  from that obtain d where "fst x = fst (normalize_quot x) * d"
    and "snd x = snd (normalize_quot x) * d" and "d \<noteq> 0"
    by (rule normalize_quotE')
  then show ?thesis
    by (simp add: fps_of_poly_mult)
qed

lemma fps_of_poly_quot_normalize_quot' [simp]:
  "fps_of_poly (fst (normalize_quot x)) / fps_of_poly (snd (normalize_quot x)) =
     fps_of_poly (fst x) / fps_of_poly (snd x)"
  if "coeff (snd x) 0 \<noteq> (0 :: 'a :: {field,factorial_ring_gcd})"
  using that by (auto intro: fps_of_poly_quot_normalize_quot)

lift_definition fps_of_ratfps :: "'a :: {field,factorial_ring_gcd} ratfps \<Rightarrow> 'a fps" is
  "\<lambda>x. fps_of_poly (numerator x) / fps_of_poly (denominator x)" .

lemma fps_of_ratfps_altdef: 
  "fps_of_ratfps x = (case quot_of_ratfps x of (a, b) \<Rightarrow> fps_of_poly a / fps_of_poly b)"
  by transfer (simp add: case_prod_unfold)

lemma fps_of_ratfps_ratfps_of_poly [simp]: "fps_of_ratfps (ratfps_of_poly p) = fps_of_poly p"
  by transfer simp

lemma fps_of_ratfps_0 [simp]: "fps_of_ratfps 0 = 0"
  by transfer simp
  
lemma fps_of_ratfps_1 [simp]: "fps_of_ratfps 1 = 1"
  by transfer simp

lemma fps_of_ratfps_uminus [simp]: "fps_of_ratfps (-x) = - fps_of_ratfps x"
  by transfer (simp add: quot_of_fract_uminus case_prod_unfold Let_def fps_of_poly_simps dvd_neg_div)
  
lemma fps_of_ratfps_add [simp]: "fps_of_ratfps (x + y) = fps_of_ratfps x + fps_of_ratfps y"
  by transfer (simp add: quot_of_fract_add Let_def case_prod_unfold fps_of_poly_simps)

lemma fps_of_ratfps_diff [simp]: "fps_of_ratfps (x - y) = fps_of_ratfps x - fps_of_ratfps y"
  by transfer (simp add: quot_of_fract_diff Let_def case_prod_unfold fps_of_poly_simps)

lemma is_unit_div_div_commute: "is_unit b \<Longrightarrow> is_unit c \<Longrightarrow> a div b div c = a div c div b"
  by (metis is_unit_div_mult2_eq mult.commute)

lemma fps_of_ratfps_mult [simp]: "fps_of_ratfps (x * y) = fps_of_ratfps x * fps_of_ratfps y"
proof (transfer, goal_cases)
  case (1 x y)
  moreover define x' y' where "x' = quot_of_fract x" and "y' = quot_of_fract y"
  ultimately have assms: "coeff (snd x') 0 \<noteq> 0" "coeff (snd y') 0 \<noteq> 0"
    by simp_all
  moreover define w z where "w = normalize_quot (fst x', snd y')" and "z = normalize_quot (fst y', snd x')"
  ultimately have unit: "coeff (snd x') 0 \<noteq> 0" "coeff (snd y') 0 \<noteq> 0" 
    "coeff (snd w) 0 \<noteq> 0" "coeff (snd z) 0 \<noteq> 0"
    by (simp_all add: coeff_0_normalize_quot_nonzero)
  have "fps_of_poly (fst w * fst z) / fps_of_poly (snd w * snd z) =
          (fps_of_poly (fst w) / fps_of_poly (snd w)) *
          (fps_of_poly (fst z) / fps_of_poly (snd z))" (is "_ = ?A * ?B")
    by (simp add: is_unit_div_mult2_eq fps_of_poly_mult unit_div_mult_swap unit_div_commute unit)
  also have "\<dots> = (fps_of_poly (fst x') / fps_of_poly (snd x')) * 
                    (fps_of_poly (fst y') / fps_of_poly (snd y'))" using unit 
    by (simp add: w_def z_def unit_div_commute unit_div_mult_swap is_unit_div_div_commute)
  finally show ?case
    by (simp add: w_def z_def x'_def y'_def Let_def case_prod_unfold quot_of_fract_mult mult_ac)
qed

lemma div_const_unit_poly: "is_unit c \<Longrightarrow> p div [:c:] = smult (1 div c) p"
  by (simp add: is_unit_const_poly_iff unit_eq_div1)

lemma normalize_field: 
  "normalize (x :: 'a :: {normalization_semidom,field}) = (if x = 0 then 0 else 1)"
  by (auto simp: normalize_1_iff dvd_field_iff)

lemma unit_factor_field [simp]:
  "unit_factor (x :: 'a :: {normalization_semidom,field}) = x"
  using unit_factor_mult_normalize[of x] normalize_field[of x]
  by (simp split: if_splits)

lemma fps_of_poly_normalize_field: 
  "fps_of_poly (normalize (p :: 'a :: {field, normalization_semidom} poly)) = 
     fps_of_poly p * fps_const (inverse (lead_coeff p))"
  by (cases "p = 0")
     (simp_all add: normalize_poly_def div_const_unit_poly divide_simps dvd_field_iff)

lemma unit_factor_poly_altdef: "unit_factor p = monom (unit_factor (lead_coeff p)) 0"
  by (simp add: unit_factor_poly_def monom_altdef)

lemma div_const_poly: "p div [:c::'a::field:] = smult (inverse c) p"
  by (cases "c = 0") (simp_all add: unit_eq_div1 is_unit_triv)

lemma fps_of_ratfps_inverse [simp]: "fps_of_ratfps (inverse x) = inverse (fps_of_ratfps x)"
proof (transfer, goal_cases)
  case (1 x)
  hence "smult (lead_coeff (fst (quot_of_fract x))) (snd (quot_of_fract x)) div
           unit_factor (fst (quot_of_fract x)) = snd (quot_of_fract x)"
    if "fst (quot_of_fract x) \<noteq> 0" using that
    by (simp add: unit_factor_poly_altdef monom_0 div_const_poly)
  with 1 show ?case
    by (auto simp: Let_def case_prod_unfold fps_divide_unit fps_inverse_mult
          quot_of_fract_inverse mult_ac
          fps_of_poly_simps fps_const_inverse
          fps_of_poly_normalize_field div_smult_left [symmetric])
qed

context
  includes fps_notation
begin

lemma ratfps_nth_altdef: "ratfps_nth x n = fps_of_ratfps x $ n" 
  by transfer
     (simp_all add: case_prod_unfold fps_divide_unit fps_times_def fps_inverse_def 
        ratfps_nth_aux_correct Let_def)

lemma fps_of_ratfps_is_unit: "fps_of_ratfps a $ 0 \<noteq> 0 \<longleftrightarrow> ratfps_nth a 0 \<noteq> 0"
  by (simp add: ratfps_nth_altdef)

lemma ratfps_nth_0 [simp]: "ratfps_nth 0 n = 0"
  by (simp add: ratfps_nth_altdef)

lemma fps_of_ratfps_cases:
  obtains p q where "coeff q 0 \<noteq> 0" "fps_of_ratfps f = fps_of_poly p / fps_of_poly q"
  by (rule that[of "snd (quot_of_ratfps f)" "fst (quot_of_ratfps f)"])
     (simp_all add: fps_of_ratfps_altdef case_prod_unfold)

lemma fps_of_ratfps_cutoff [simp]:
    "fps_of_poly (ratfps_cutoff n x) = fps_cutoff n (fps_of_ratfps x)"
  by (simp add: fps_eq_iff ratfps_cutoff_def nth_default_def ratfps_nth_altdef)

lemma subdegree_fps_of_ratfps:
  "subdegree (fps_of_ratfps x) = ratfps_subdegree x"
  by transfer (simp_all add: case_prod_unfold subdegree_div_unit poly_subdegree_def)

lemma ratfps_subdegree_altdef:
  "ratfps_subdegree x = subdegree (fps_of_ratfps x)"
  using subdegree_fps_of_ratfps ..

end


code_datatype fps_of_ratfps
  
lemma fps_zero_code [code]: "0 = fps_of_ratfps 0" by simp
  
lemma fps_one_code [code]: "1 = fps_of_ratfps 1" by simp

lemma fps_const_code [code]: "fps_const c = fps_of_poly [:c:]" by simp

lemma fps_of_poly_code [code]: "fps_of_poly p = fps_of_ratfps (ratfps_of_poly p)" by simp
  
lemma fps_X_code [code]: "fps_X = fps_of_ratfps (ratfps_of_poly [:0,1:])" by simp

lemma fps_nth_code [code]: "fps_nth (fps_of_ratfps x) n = ratfps_nth x n"
  by (simp add: ratfps_nth_altdef)
     
lemma fps_uminus_code [code]: "- fps_of_ratfps x = fps_of_ratfps (-x)" by simp
  
lemma fps_add_code [code]: "fps_of_ratfps x + fps_of_ratfps y = fps_of_ratfps (x + y)" by simp

lemma fps_diff_code [code]: "fps_of_ratfps x - fps_of_ratfps y = fps_of_ratfps (x - y)" by simp

lemma fps_mult_code [code]: "fps_of_ratfps x * fps_of_ratfps y = fps_of_ratfps (x * y)" by simp

lemma fps_inverse_code [code]: "inverse (fps_of_ratfps x) = fps_of_ratfps (inverse x)" 
  by simp

lemma fps_cutoff_code [code]: "fps_cutoff n (fps_of_ratfps x) = fps_of_poly (ratfps_cutoff n x)"
  by simp
  
lemmas subdegree_code [code] = subdegree_fps_of_ratfps

 
lemma fractrel_normalize_quot:
  "fractrel p p \<Longrightarrow> fractrel q q \<Longrightarrow> 
     fractrel (normalize_quot p) (normalize_quot q) \<longleftrightarrow> fractrel p q"
  by (subst fractrel_normalize_quot_left fractrel_normalize_quot_right, simp)+ (rule refl)
  
lemma fps_of_ratfps_eq_iff [simp]:
  "fps_of_ratfps p = fps_of_ratfps q \<longleftrightarrow> p = q"
proof -
  {
    fix p q :: "'a poly fract"
    assume "fractrel (quot_of_fract p) (quot_of_fract q)"
    hence "p = q" by transfer (simp only: fractrel_normalize_quot)
  } note A = this
  show ?thesis        
    by transfer (auto simp: case_prod_unfold unit_eq_div1 unit_eq_div2 unit_div_commute intro: A)
qed
  
lemma fps_of_ratfps_eq_zero_iff [simp]:
  "fps_of_ratfps p = 0 \<longleftrightarrow> p = 0" 
  by (simp del: fps_of_ratfps_0 add: fps_of_ratfps_0 [symmetric])

lemma unit_factor_snd_quot_of_ratfps [simp]: 
  "unit_factor (snd (quot_of_ratfps x)) = 1"
  by transfer simp
  
lemma poly_shift_times_monom_le: 
  "n \<le> m \<Longrightarrow> poly_shift n (monom c m * p) = monom c (m - n) * p"
  by (intro poly_eqI) (auto simp: coeff_monom_mult coeff_poly_shift)

lemma poly_shift_times_monom_ge: 
  "n \<ge> m \<Longrightarrow> poly_shift n (monom c m * p) = smult c (poly_shift (n - m) p)"
  by (intro poly_eqI) (auto simp: coeff_monom_mult coeff_poly_shift)
  
lemma poly_shift_times_monom:
  "poly_shift n (monom c n * p) = smult c p"
  by (intro poly_eqI) (auto simp: coeff_monom_mult coeff_poly_shift)

lemma monom_times_poly_shift:
  assumes "poly_subdegree p \<ge> n"
  shows   "monom c n * poly_shift n p = smult c p" (is "?lhs = ?rhs")
proof (intro poly_eqI) 
  fix k
  show "coeff ?lhs k = coeff ?rhs k"
  proof (cases "k < n")
    case True
    with assms have "k < poly_subdegree p" by simp
    hence "coeff p k = 0" by (simp add: coeff_less_poly_subdegree)
    thus ?thesis by (auto simp: coeff_monom_mult coeff_poly_shift)
  qed (auto simp: coeff_monom_mult coeff_poly_shift)
qed

lemma monom_times_poly_shift':
  assumes "poly_subdegree p \<ge> n"
  shows   "monom (1 :: 'a :: comm_semiring_1) n * poly_shift n p = p"
  by (simp add: monom_times_poly_shift[OF assms])

lemma subdegree_minus_cutoff_ge:
  assumes "f - fps_cutoff n (f :: 'a :: ab_group_add fps) \<noteq> 0"
  shows   "subdegree (f - fps_cutoff n f) \<ge> n"
  using assms by (rule subdegree_geI) simp_all

lemma fps_shift_times_X_power'': "fps_shift n (fps_X ^ n * f :: 'a :: comm_ring_1 fps) = f"
  using fps_shift_times_fps_X_power'[of n f] by (simp add: mult.commute)
  
lemma 
  ratfps_shift_code [code abstract]:
    "quot_of_ratfps (ratfps_shift n x) = 
       (let (a, b) = quot_of_ratfps (x - ratfps_of_poly (ratfps_cutoff n x))
        in  (poly_shift n a, b))" (is "?lhs1 = ?rhs1") and
  fps_of_ratfps_shift [simp]:
    "fps_of_ratfps (ratfps_shift n x) = fps_shift n (fps_of_ratfps x)"   
proof -
  include fps_notation
  define x' where "x' = ratfps_of_poly (ratfps_cutoff n x)"
  define y where "y = quot_of_ratfps (x - x')"
  
  have "coprime (fst y) (snd y)" unfolding y_def
    by transfer (rule coprime_quot_of_fract)
  also have fst_y: "fst y = monom 1 n * poly_shift n (fst y)"
  proof (cases "x = x'")
    case False
    have "poly_subdegree (fst y) = subdegree (fps_of_poly (fst y))"
      by (simp add: poly_subdegree_def)
    also have "\<dots> = subdegree (fps_of_poly (fst y) / fps_of_poly (snd y))"
      by (subst subdegree_div_unit) (simp_all add: y_def)
    also have "fps_of_poly (fst y) / fps_of_poly (snd y) = fps_of_ratfps (x - x')"
      unfolding y_def by transfer (simp add: case_prod_unfold)
    also from False have "subdegree \<dots> \<ge> n"
    proof (intro subdegree_geI)
      fix k assume "k < n"
      thus "fps_of_ratfps (x - x') $ k = 0" by (simp add: x'_def)
    qed simp_all
    finally show ?thesis by (rule monom_times_poly_shift' [symmetric])
  qed (simp_all add: y_def)
  finally have coprime: "coprime (poly_shift n (fst y)) (snd y)"
    by simp
  
  have "quot_of_ratfps (ratfps_shift n x) = 
          quot_of_ratfps (quot_to_ratfps (poly_shift n (fst y), snd y))"
    by (simp add: ratfps_shift_def Let_def case_prod_unfold x'_def y_def)
  also from coprime have "\<dots> = (poly_shift n (fst y), snd y)"
    by (intro quot_of_ratfps_quot_to_ratfps) (simp_all add: y_def normalized_fracts_def)
  also have "\<dots> = ?rhs1" by (simp add: case_prod_unfold Let_def y_def x'_def)
  finally show eq: "?lhs1 = ?rhs1" .
  
  have "fps_shift n (fps_of_ratfps x) = fps_shift n (fps_of_ratfps (x - x'))"
    by (intro fps_ext) (simp_all add: x'_def)
  also have "fps_of_ratfps (x - x') = fps_of_poly (fst y) / fps_of_poly (snd y)"
    by (simp add: fps_of_ratfps_altdef y_def case_prod_unfold)
  also have "fps_shift n \<dots> = fps_of_ratfps (ratfps_shift n x)"
    by (subst fst_y, subst fps_of_poly_mult, subst unit_div_mult_swap [symmetric])
       (simp_all add: y_def fps_of_poly_monom fps_shift_times_X_power'' eq 
          fps_of_ratfps_altdef case_prod_unfold Let_def x'_def)
  finally show "fps_of_ratfps (ratfps_shift n x) = fps_shift n (fps_of_ratfps x)" ..
qed

lemma fps_shift_code [code]: "fps_shift n (fps_of_ratfps x) = fps_of_ratfps (ratfps_shift n x)"
  by simp

instantiation fps :: (equal) equal
begin

definition equal_fps :: "'a fps \<Rightarrow> 'a fps \<Rightarrow> bool" where
  [simp]: "equal_fps f g \<longleftrightarrow> f = g"

instance by standard simp_all

end

lemma equal_fps_code [code]: "HOL.equal (fps_of_ratfps f) (fps_of_ratfps g) \<longleftrightarrow> f = g"
  by simp

lemma fps_of_ratfps_divide [simp]:
  "fps_of_ratfps (f div g) = fps_of_ratfps f div fps_of_ratfps g"
  unfolding fps_divide_def Let_def by transfer' (simp add: Let_def ratfps_subdegree_altdef)
           
lemma ratfps_eqI: "fps_of_ratfps x = fps_of_ratfps y \<Longrightarrow> x = y" by simp

instance ratfps :: ("{field,factorial_ring_gcd}") algebraic_semidom
  by standard (auto intro: ratfps_eqI)

lemma fps_of_ratfps_dvd [simp]:
  "fps_of_ratfps x dvd fps_of_ratfps y \<longleftrightarrow> x dvd y"
proof
  assume "fps_of_ratfps x dvd fps_of_ratfps y"
  hence "fps_of_ratfps y = fps_of_ratfps y div fps_of_ratfps x * fps_of_ratfps x" by simp
  also have "\<dots> = fps_of_ratfps (y div x * x)" by simp
  finally have "y = y div x * x" by (subst (asm) fps_of_ratfps_eq_iff)
  thus "x dvd y" by (intro dvdI[of _ _ "y div x"]) (simp add: mult_ac)
next
  assume "x dvd y"
  hence "y = y div x * x" by simp
  also have "fps_of_ratfps \<dots> = fps_of_ratfps (y div x) * fps_of_ratfps x" by simp
  finally show "fps_of_ratfps x dvd fps_of_ratfps y" by (simp del: fps_of_ratfps_divide)
qed

lemma is_unit_ratfps_iff [simp]:
  "is_unit x \<longleftrightarrow> ratfps_nth x 0 \<noteq> 0"
proof
  assume "is_unit x"
  then obtain y where "1 = x * y" by (auto elim!: dvdE)
  hence "1 = fps_of_ratfps (x * y)" by (simp del: fps_of_ratfps_mult)
  also have "\<dots> = fps_of_ratfps x * fps_of_ratfps y" by simp
  finally have "is_unit (fps_of_ratfps x)" by (rule dvdI[of _ _ "fps_of_ratfps y"])
  thus "ratfps_nth x 0 \<noteq> 0" by (simp add: ratfps_nth_altdef)
next
  assume "ratfps_nth x 0 \<noteq> 0"
  hence "fps_of_ratfps (x * inverse x) = 1"
    by (simp add: ratfps_nth_altdef inverse_mult_eq_1')
  also have "\<dots> = fps_of_ratfps 1" by simp
  finally have "x * inverse x = 1" by (subst (asm) fps_of_ratfps_eq_iff)
  thus "is_unit x" by (intro dvdI[of _ _ "inverse x"]) simp_all
qed

instantiation ratfps :: ("{field,factorial_ring_gcd}") normalization_semidom
begin

definition unit_factor_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps" where
  "unit_factor x = ratfps_shift (ratfps_subdegree x) x"

definition normalize_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps" where
  "normalize x = (if x = 0 then 0 else ratfps_of_poly (monom 1 (ratfps_subdegree x)))"

lemma fps_of_ratfps_unit_factor [simp]: 
  "fps_of_ratfps (unit_factor x) = unit_factor (fps_of_ratfps x)"
  unfolding unit_factor_ratfps_def by (simp add: ratfps_subdegree_altdef)

lemma fps_of_ratfps_normalize [simp]: 
  "fps_of_ratfps (normalize x) = normalize (fps_of_ratfps x)"
  unfolding normalize_ratfps_def by (simp add: fps_of_poly_monom ratfps_subdegree_altdef)

instance proof
  show "unit_factor x * normalize x = x" "normalize (0 :: 'a ratfps) = 0" 
       "unit_factor (0 :: 'a ratfps) = 0" for x :: "'a ratfps"
    by (rule ratfps_eqI, simp add: ratfps_subdegree_code 
          del: fps_of_ratfps_eq_iff fps_unit_factor_def fps_normalize_def)+
  show "is_unit (unit_factor a)" if "a \<noteq> 0" for a :: "'a ratfps"
    using that by (auto simp: ratfps_nth_altdef)
  show "unit_factor (a * b) = unit_factor a * unit_factor b" for a b :: "'a ratfps"
    by (rule ratfps_eqI, insert unit_factor_mult[of "fps_of_ratfps a" "fps_of_ratfps b"])
       (simp del: fps_of_ratfps_eq_iff)
  show "unit_factor a = a" if "is_unit a" for a :: "'a ratfps"
    by (rule ratfps_eqI) (insert that, auto simp: fps_of_ratfps_is_unit)
qed

end

instantiation ratfps :: ("{field,factorial_ring_gcd}") semidom_modulo
begin

lift_definition modulo_ratfps :: "'a ratfps \<Rightarrow> 'a ratfps \<Rightarrow> 'a ratfps" is
  "\<lambda>f g. if g = 0 then f else 
           let n = ratfps_subdegree g; h = ratfps_shift n g
           in  ratfps_of_poly (ratfps_cutoff n (f * inverse h)) * h" .

lemma fps_of_ratfps_mod [simp]: 
   "fps_of_ratfps (f mod g :: 'a ratfps) = fps_of_ratfps f mod fps_of_ratfps g"
  unfolding fps_mod_def by transfer' (simp add: Let_def ratfps_subdegree_altdef)

instance
  by standard (auto intro: ratfps_eqI)

end

instantiation ratfps :: ("{field,factorial_ring_gcd}") euclidean_ring
begin

definition euclidean_size_ratfps :: "'a ratfps \<Rightarrow> nat" where
  "euclidean_size_ratfps x = (if x = 0 then 0 else 2 ^ ratfps_subdegree x)"
  
lemma fps_of_ratfps_euclidean_size [simp]:
  "euclidean_size x = euclidean_size (fps_of_ratfps x)"
  unfolding euclidean_size_ratfps_def fps_euclidean_size_def
  by (simp add: ratfps_subdegree_altdef)

instance proof
  show "euclidean_size (0 :: 'a ratfps) = 0" by simp
  show "euclidean_size (a mod b) < euclidean_size b"
       "euclidean_size a \<le> euclidean_size (a * b)" if "b \<noteq> 0" for a b :: "'a ratfps"
    using that by (simp_all add: mod_size_less size_mult_mono)
qed

end

instantiation ratfps :: ("{field,factorial_ring_gcd}") euclidean_ring_cancel
begin

instance
  by standard (auto intro: ratfps_eqI)

end

lemma quot_of_ratfps_eq_iff [simp]: "quot_of_ratfps x = quot_of_ratfps y \<longleftrightarrow> x = y"
  by transfer simp

lemma ratfps_eq_0_code: "x = 0 \<longleftrightarrow> fst (quot_of_ratfps x) = 0"
proof
  assume "fst (quot_of_ratfps x) = 0"
  moreover have "coprime (fst (quot_of_ratfps x)) (snd (quot_of_ratfps x))"
    by transfer (simp add: coprime_quot_of_fract)
  moreover have "normalize (snd (quot_of_ratfps x)) = snd (quot_of_ratfps x)"
    by (simp add: div_unit_factor [symmetric] del: div_unit_factor)
  ultimately have "quot_of_ratfps x = (0,1)"
    by (simp add: prod_eq_iff normalize_idem_imp_is_unit_iff)
  also have "\<dots> = quot_of_ratfps 0" by simp
  finally show "x = 0" by (subst (asm) quot_of_ratfps_eq_iff)
qed simp_all

lemma fps_dvd_code [code_unfold]:
  "x dvd y \<longleftrightarrow> y = 0 \<or> ((x::'a::{field,factorial_ring_gcd} fps) \<noteq> 0 \<and> subdegree x \<le> subdegree y)"
  using fps_dvd_iff[of x y] by (cases "x = 0") auto

lemma ratfps_dvd_code [code_unfold]: 
  "x dvd y \<longleftrightarrow> y = 0 \<or> (x \<noteq> 0 \<and> ratfps_subdegree x \<le> ratfps_subdegree y)"
  using fps_dvd_code [of "fps_of_ratfps x" "fps_of_ratfps y"]
  by (simp add: ratfps_subdegree_altdef)

instance ratfps :: ("{field,factorial_ring_gcd}") normalization_euclidean_semiring ..

instantiation ratfps :: ("{field,factorial_ring_gcd}") euclidean_ring_gcd
begin

definition "gcd_ratfps = (Euclidean_Algorithm.gcd :: 'a ratfps \<Rightarrow> _)"
definition "lcm_ratfps = (Euclidean_Algorithm.lcm :: 'a ratfps \<Rightarrow> _)"
definition "Gcd_ratfps = (Euclidean_Algorithm.Gcd :: 'a ratfps set \<Rightarrow> _)"
definition "Lcm_ratfps = (Euclidean_Algorithm.Lcm:: 'a ratfps set \<Rightarrow> _)"

instance by standard (simp_all add: gcd_ratfps_def lcm_ratfps_def Gcd_ratfps_def Lcm_ratfps_def)
end

lemma ratfps_eq_0_iff: "x = 0 \<longleftrightarrow> fps_of_ratfps x = 0"
  using fps_of_ratfps_eq_iff[of x 0] unfolding fps_of_ratfps_0 by simp

lemma ratfps_of_poly_eq_0_iff: "ratfps_of_poly x = 0 \<longleftrightarrow> x = 0"
  by (auto simp: ratfps_eq_0_iff)



lemma ratfps_gcd:
  assumes [simp]: "f \<noteq> 0" "g \<noteq> 0"
  shows   "gcd f g = ratfps_of_poly (monom 1 (min (ratfps_subdegree f) (ratfps_subdegree g)))"
  by (rule sym, rule gcdI)
     (auto simp: ratfps_subdegree_altdef ratfps_dvd_code subdegree_fps_of_poly
         ratfps_of_poly_eq_0_iff normalize_ratfps_def)

lemma ratfps_gcd_altdef: "gcd (f :: 'a :: {field,factorial_ring_gcd} ratfps) g =
  (if f = 0 \<and> g = 0 then 0 else
   if f = 0 then ratfps_of_poly (monom 1 (ratfps_subdegree g)) else
   if g = 0 then ratfps_of_poly (monom 1 (ratfps_subdegree f)) else
     ratfps_of_poly (monom 1 (min (ratfps_subdegree f) (ratfps_subdegree g))))"
  by (simp add: ratfps_gcd normalize_ratfps_def)

lemma ratfps_lcm:
  assumes [simp]: "f \<noteq> 0" "g \<noteq> 0"
  shows   "lcm f g = ratfps_of_poly (monom 1 (max (ratfps_subdegree f) (ratfps_subdegree g)))"
  by (rule sym, rule lcmI)
     (auto simp: ratfps_subdegree_altdef ratfps_dvd_code subdegree_fps_of_poly
         ratfps_of_poly_eq_0_iff normalize_ratfps_def)

lemma ratfps_lcm_altdef: "lcm (f :: 'a :: {field,factorial_ring_gcd} ratfps) g =
  (if f = 0 \<or> g = 0 then 0 else 
     ratfps_of_poly (monom 1 (max (ratfps_subdegree f) (ratfps_subdegree g))))"
  by (simp add: ratfps_lcm)

lemma ratfps_Gcd:
  assumes "A - {0} \<noteq> {}"
  shows   "Gcd A = ratfps_of_poly (monom 1 (INF f\<in>A-{0}. ratfps_subdegree f))"
proof (rule sym, rule GcdI)
  fix f assume "f \<in> A"
  thus "ratfps_of_poly (monom 1 (INF f\<in>A - {0}. ratfps_subdegree f)) dvd f"
    by (cases "f = 0") (auto simp: ratfps_dvd_code ratfps_of_poly_eq_0_iff ratfps_subdegree_altdef
                          subdegree_fps_of_poly intro!: cINF_lower)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> d dvd f"
  from assms obtain f where "f \<in> A - {0}" by auto
  with d[of f] have [simp]: "d \<noteq> 0" by auto
  from d assms have "ratfps_subdegree d \<le> (INF f\<in>A-{0}. ratfps_subdegree f)"
    by (intro cINF_greatest) (auto simp: ratfps_dvd_code)
  with d assms show "d dvd ratfps_of_poly (monom 1 (INF f\<in>A-{0}. ratfps_subdegree f))" 
    by (simp add: ratfps_dvd_code ratfps_subdegree_altdef subdegree_fps_of_poly)
qed (simp_all add: ratfps_subdegree_altdef subdegree_fps_of_poly normalize_ratfps_def)

lemma ratfps_Gcd_altdef: "Gcd (A :: 'a :: {field,factorial_ring_gcd} ratfps set) =
  (if A \<subseteq> {0} then 0 else ratfps_of_poly (monom 1 (INF f\<in>A-{0}. ratfps_subdegree f)))"
  using ratfps_Gcd by auto

lemma ratfps_Lcm:
  assumes "A \<noteq> {}" "0 \<notin> A" "bdd_above (ratfps_subdegree`A)"
  shows   "Lcm A = ratfps_of_poly (monom 1 (SUP f\<in>A. ratfps_subdegree f))"
proof (rule sym, rule LcmI)
  fix f assume "f \<in> A"
  moreover from assms(3) have "bdd_above (ratfps_subdegree ` A)" by auto
  ultimately show "f dvd ratfps_of_poly (monom 1 (SUP f\<in>A. ratfps_subdegree f))" using assms(2)
    by (cases "f = 0") (auto simp: ratfps_dvd_code ratfps_of_poly_eq_0_iff subdegree_fps_of_poly 
                          ratfps_subdegree_altdef [abs_def] intro!: cSUP_upper)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> f dvd d"
  from assms obtain f where f: "f \<in> A" "f \<noteq> 0" by auto
  show "ratfps_of_poly (monom 1 (SUP f\<in>A. ratfps_subdegree f)) dvd d"
  proof (cases "d = 0")
    assume "d \<noteq> 0"
    moreover from d have "\<And>f. f \<in> A \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> f dvd d" by blast
    ultimately have "ratfps_subdegree d \<ge> (SUP f\<in>A. ratfps_subdegree f)" using assms
      by (intro cSUP_least) (auto simp: ratfps_dvd_code)
    with \<open>d \<noteq> 0\<close> show ?thesis by (simp add: ratfps_dvd_code ratfps_of_poly_eq_0_iff 
          ratfps_subdegree_altdef subdegree_fps_of_poly)
  qed simp_all
qed (simp_all add: ratfps_subdegree_altdef subdegree_fps_of_poly normalize_ratfps_def)

lemma ratfps_Lcm_altdef:
  "Lcm (A :: 'a :: {field,factorial_ring_gcd} ratfps set) =
     (if 0 \<in> A \<or> \<not>bdd_above (ratfps_subdegree`A) then 0 else
      if A = {} then 1 else ratfps_of_poly (monom 1 (SUP f\<in>A. ratfps_subdegree f)))"
proof (cases "bdd_above (ratfps_subdegree`A)")
  assume unbounded: "\<not>bdd_above (ratfps_subdegree`A)"
  have "Lcm A = 0"
  proof (rule ccontr)
    assume "Lcm A \<noteq> 0"
    from unbounded obtain f where f: "f \<in> A" "ratfps_subdegree (Lcm A) < ratfps_subdegree f"
      unfolding bdd_above_def by (auto simp: not_le)
    moreover from this and \<open>Lcm A \<noteq> 0\<close> have "ratfps_subdegree f \<le> ratfps_subdegree (Lcm A)"
      using dvd_Lcm[of f A] by (auto simp: ratfps_dvd_code)
    ultimately show False by simp
  qed
  with unbounded show ?thesis by simp
qed (simp_all add: ratfps_Lcm Lcm_eq_0_I)

lemma fps_of_ratfps_quot_to_ratfps:
  "coeff y 0 \<noteq> 0 \<Longrightarrow> fps_of_ratfps (quot_to_ratfps (x,y)) = fps_of_poly x / fps_of_poly y"
proof (transfer, goal_cases)
  case (1 y x)
  define x' y' where "x' = fst (normalize_quot (x,y))" and "y' = snd (normalize_quot (x,y))"
  from 1 have nz: "y \<noteq> 0" by auto
  have eq: "normalize_quot (x', y') = (x', y')" by (simp add: x'_def y'_def)
  from normalize_quotE[OF nz, of x] guess d . note d = this [folded x'_def y'_def]
  have "(case quot_of_fract (if coeff y' 0 = 0 then 0 else quot_to_fract (x', y')) of
          (a, b) \<Rightarrow> fps_of_poly a / fps_of_poly b) = fps_of_poly x / fps_of_poly y"
    using d eq 1 by (auto simp: case_prod_unfold fps_of_poly_simps quot_of_fract_quot_to_fract 
                                Let_def coeff_0_mult)
  thus ?case by (auto simp add: Let_def case_prod_unfold x'_def y'_def)
qed

lemma fps_of_ratfps_quot_to_ratfps_code_post1:
  "fps_of_ratfps (quot_to_ratfps (x,pCons 1 y)) = fps_of_poly x / fps_of_poly (pCons 1 y)"
  "fps_of_ratfps (quot_to_ratfps (x,pCons (-1) y)) = fps_of_poly x / fps_of_poly (pCons (-1) y)"
  by (simp_all add: fps_of_ratfps_quot_to_ratfps)

lemma fps_of_ratfps_quot_to_ratfps_code_post2:
  "fps_of_ratfps (quot_to_ratfps (x'::'a::{field_char_0,factorial_ring_gcd} poly,pCons (numeral n) y')) = 
     fps_of_poly x' / fps_of_poly (pCons (numeral n) y')"
  "fps_of_ratfps (quot_to_ratfps (x'::'a::{field_char_0,factorial_ring_gcd} poly,pCons (-numeral n) y')) = 
     fps_of_poly x' / fps_of_poly (pCons (-numeral n) y')"
  by (simp_all add: fps_of_ratfps_quot_to_ratfps)

lemmas fps_of_ratfps_quot_to_ratfps_code_post [code_post] =
  fps_of_ratfps_quot_to_ratfps_code_post1
  fps_of_ratfps_quot_to_ratfps_code_post2

lemma fps_dehorner: 
  fixes a b c :: "'a :: semiring_1 fps" and d e f :: "'b :: ring_1 fps"
  shows
  "(b + c) * fps_X = b * fps_X + c * fps_X" "(a * fps_X) * fps_X = a * fps_X ^ 2" 
  "a * fps_X ^ m * fps_X = a * fps_X ^ (Suc m)" "a * fps_X * fps_X ^ m = a * fps_X ^ (Suc m)" 
  "a * fps_X^m * fps_X^n = a * fps_X^(m+n)" "a + (b + c) = a + b + c" "a * 1 = a" "1 * a = a"
  "d + - e = d - e" "(-d) * e = - (d * e)" "d + (e - f) = d + e - f"
  "(d - e) * fps_X = d * fps_X - e * fps_X" "fps_X * fps_X = fps_X^2" "fps_X * fps_X^m = fps_X^(Suc m)" "fps_X^m * fps_X = fps_X^Suc m"
  "fps_X^m * fps_X^n = fps_X^(m + n)"
  by (simp_all add: algebra_simps power2_eq_square power_add power_commutes)

lemma fps_divide_1: "(a :: 'a :: field fps) / 1 = a" by simp

lemmas fps_of_poly_code_post [code_post] = 
  fps_of_poly_simps fps_const_0_eq_0 fps_const_1_eq_1 numeral_fps_const [symmetric]
  fps_const_neg [symmetric] fps_const_divide [symmetric]
  fps_dehorner Suc_numeral arith_simps fps_divide_1



definition (in term_syntax)
  valterm_ratfps :: 
    "'a ::{field,factorial_ring_gcd,typerep} poly \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> 
     'a poly \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> 'a ratfps \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "valterm_ratfps k l = 
    Code_Evaluation.valtermify (/) {\<cdot>} 
      (Code_Evaluation.valtermify ratfps_of_poly {\<cdot>} k) {\<cdot>} 
      (Code_Evaluation.valtermify ratfps_of_poly {\<cdot>} l)"


notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation ratfps :: ("{field,factorial_ring_gcd,random}") random
begin

definition
  "Quickcheck_Random.random i = 
     Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>num::'a poly \<times> (unit \<Rightarrow> term). 
       Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>denom::'a poly \<times> (unit \<Rightarrow> term). 
         Pair (let denom = (if fst denom = 0 then Code_Evaluation.valtermify 1 else denom)
               in  valterm_ratfps num denom)))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation ratfps :: ("{field,factorial_ring_gcd,exhaustive}") exhaustive
begin

definition
  "exhaustive_ratfps f d = 
     Quickcheck_Exhaustive.exhaustive (\<lambda>num. 
       Quickcheck_Exhaustive.exhaustive (\<lambda>denom. f (
         let denom = if denom = 0 then 1 else denom
         in  ratfps_of_poly num / ratfps_of_poly denom)) d) d"

instance ..

end

instantiation ratfps :: ("{field,factorial_ring_gcd,full_exhaustive}") full_exhaustive
begin

definition
  "full_exhaustive_ratfps f d = 
     Quickcheck_Exhaustive.full_exhaustive (\<lambda>num::'a poly \<times> (unit \<Rightarrow> term).
       Quickcheck_Exhaustive.full_exhaustive (\<lambda>denom::'a poly \<times> (unit \<Rightarrow> term).
         f (let denom = if fst denom = 0 then Code_Evaluation.valtermify 1 else denom
            in  valterm_ratfps num denom)) d) d"

instance ..

end 

quickcheck_generator fps constructors: fps_of_ratfps

end
