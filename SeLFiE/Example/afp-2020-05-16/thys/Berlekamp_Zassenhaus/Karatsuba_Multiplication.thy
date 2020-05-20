(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Karatsuba's Multiplication Algorithm for Polynomials\<close>
theory Karatsuba_Multiplication
imports 
  Polynomial_Interpolation.Missing_Polynomial
begin

lemma karatsuba_main_step: fixes f :: "'a :: comm_ring_1 poly"
  assumes f: "f = monom_mult n f1 + f0" and g: "g = monom_mult n g1 + g0" 
  shows 
    "monom_mult (n + n) (f1 * g1) + (monom_mult n (f1 * g1 - (f1 - f0) * (g1 - g0) + f0 * g0) + f0 * g0) = f * g"
  unfolding assms
  by (auto simp: field_simps mult_monom monom_mult_def)  

lemma karatsuba_single_sided: fixes f :: "'a :: comm_ring_1 poly" 
  assumes "f = monom_mult n f1 + f0"
  shows "monom_mult n (f1 * g) + f0 * g = f * g"
  unfolding assms by (auto simp: field_simps mult_monom monom_mult_def)  


definition split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where 
  [code del]: "split_at n xs = (take n xs, drop n xs)" 
  
lemma split_at_code[code]: 
  "split_at n [] = ([],[])"
  "split_at n (x # xs) = (if n = 0 then ([], x # xs) else case split_at (n-1) xs of (bef,aft)
    \<Rightarrow> (x # bef, aft))"
  unfolding split_at_def by (force, cases n, auto)

fun coeffs_minus :: "'a :: ab_group_add list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "coeffs_minus (x # xs) (y # ys) = ((x - y) # coeffs_minus xs ys)" 
| "coeffs_minus xs [] = xs" 
| "coeffs_minus [] ys = map uminus ys" 
  
text \<open>The following constant determines at which size we will switch to the standard 
   multiplication algorithm.\<close>
definition karatsuba_lower_bound where [termination_simp]: "karatsuba_lower_bound = (7 :: nat)" 

fun karatsuba_main :: "'a :: comm_ring_1 list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "karatsuba_main f n g m = (if n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound then 
    let ff = poly_of_list f in foldr (\<lambda>a p. smult a ff + pCons 0 p) g 0
   else let n2 = n div 2 in 
   if m > n2 then (case split_at n2 f of 
   (f0,f1) \<Rightarrow> case split_at n2 g of
   (g0,g1) \<Rightarrow> let 
      p1 = karatsuba_main f1 (n - n2) g1 (m - n2);
      p2 = karatsuba_main (coeffs_minus f1 f0) n2 (coeffs_minus g1 g0) n2;
      p3 = karatsuba_main f0 n2 g0 n2 
      in monom_mult (n2 + n2) p1 + (monom_mult n2 (p1 - p2 + p3) + p3))
    else case split_at n2 f of
    (f0,f1) \<Rightarrow> let 
       p1 = karatsuba_main f1 (n - n2) g m; 
       p2 = karatsuba_main f0 n2 g m
     in monom_mult n2 p1 + p2)" 

declare karatsuba_main.simps[simp del]

lemma poly_of_list_split_at: assumes "split_at n f = (f0,f1)" 
  shows "poly_of_list f = monom_mult n (poly_of_list f1) + poly_of_list f0"
proof -
  from assms have id: "f1 = drop n f" "f0 = take n f" unfolding split_at_def by auto
  show ?thesis unfolding id
  proof (rule poly_eqI)
    fix i
    show "coeff (poly_of_list f) i = 
      coeff (monom_mult n (poly_of_list (drop n f)) + poly_of_list (take n f)) i" 
      unfolding monom_mult_def coeff_monom_mult coeff_add poly_of_list_def coeff_Poly
      by (cases "n \<le> i"; cases "i \<ge> length f", auto simp: nth_default_nth nth_default_beyond)
  qed
qed
        
lemma coeffs_minus: "poly_of_list (coeffs_minus f1 f0) = poly_of_list f1 - poly_of_list f0" 
proof (rule poly_eqI, unfold poly_of_list_def coeff_diff coeff_Poly)
  fix i
  show "nth_default 0 (coeffs_minus f1 f0) i = nth_default 0 f1 i - nth_default 0 f0 i" 
  proof (induct f1 f0 arbitrary: i rule: coeffs_minus.induct)
    case (1 x xs y ys)
    thus ?case by (cases i, auto)
  next
    case (3 x xs)
    thus ?case unfolding coeffs_minus.simps
      by (subst nth_default_map_eq[of uminus 0 0], auto)    
  qed auto
qed

lemma karatsuba_main: "karatsuba_main f n g m = poly_of_list f * poly_of_list g" 
proof (induct n arbitrary: f g m rule: less_induct)
  case (less n f g m)
  note simp[simp] = karatsuba_main.simps[of f n g m]
  show ?case (is "?lhs = ?rhs")
  proof (cases "(n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound) = False")
    case False
    hence lhs: "?lhs = foldr (\<lambda>a p. smult a (poly_of_list f) + pCons 0 p) g 0" by simp
    have rhs: "?rhs = poly_of_list g * poly_of_list f" by simp 
    also have "\<dots> = foldr (\<lambda>a p. smult a (poly_of_list f) + pCons 0 p) (strip_while ((=) 0) g) 0" 
      unfolding times_poly_def fold_coeffs_def poly_of_list_impl ..
    also have "\<dots> = ?lhs" unfolding lhs 
    proof (induct g)
      case (Cons x xs)
      have "\<forall>x\<in>set xs. x = 0 \<Longrightarrow> foldr (\<lambda>a p. smult a (Poly f) + pCons 0 p) xs 0 = 0" 
        by (induct xs, auto)        
      thus ?case using Cons by (auto simp: cCons_def Cons)
    qed auto
    finally show ?thesis by simp
  next
    case True
    let ?n2 = "n div 2" 
    have "?n2 < n" "n - ?n2 < n" using True unfolding karatsuba_lower_bound_def by auto
    note IH = less[OF this(1)] less[OF this(2)]
    obtain f1 f0 where f: "split_at ?n2 f = (f0,f1)" by force
    obtain g1 g0 where g: "split_at ?n2 g = (g0,g1)" by force
    note fsplit = poly_of_list_split_at[OF f]
    note gsplit = poly_of_list_split_at[OF g]
    show "?lhs = ?rhs" unfolding simp Let_def f g split IH True if_False coeffs_minus
      karatsuba_single_sided[OF fsplit] karatsuba_main_step[OF fsplit gsplit] by auto
  qed
qed


definition karatsuba_mult_poly :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "karatsuba_mult_poly f g = (let ff = coeffs f; gg = coeffs g; n = length ff; m = length gg
    in (if n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound then if n \<le> m 
    then foldr (\<lambda>a p. smult a g + pCons 0 p) ff 0 
    else foldr (\<lambda>a p. smult a f + pCons 0 p) gg 0 
    else if n \<le> m 
    then karatsuba_main gg m ff n 
    else karatsuba_main ff n gg m))" 
  
lemma karatsuba_mult_poly: "karatsuba_mult_poly f g = f * g" 
proof -
  note d = karatsuba_mult_poly_def Let_def 
  let ?len = "length (coeffs f) \<le> length (coeffs g)" 
  show ?thesis (is "?lhs = ?rhs")
  proof (cases "length (coeffs f) \<le> karatsuba_lower_bound \<or> length (coeffs g) \<le> karatsuba_lower_bound")
    case True note outer = this
    show ?thesis
    proof (cases ?len)
      case True
      with outer have "?lhs = foldr (\<lambda>a p. smult a g + pCons 0 p) (coeffs f) 0" unfolding d by auto
      also have "\<dots> = ?rhs" unfolding times_poly_def fold_coeffs_def by auto
      finally show ?thesis .
    next
      case False
      with outer have "?lhs = foldr (\<lambda>a p. smult a f + pCons 0 p) (coeffs g) 0" unfolding d by auto
      also have "\<dots> = g * f" unfolding times_poly_def fold_coeffs_def by auto
      also have "\<dots> = ?rhs" by simp
      finally show ?thesis .
    qed
  next
    case False note outer = this
    show ?thesis
    proof (cases ?len)
      case True   
      with outer have "?lhs = karatsuba_main (coeffs g) (length (coeffs g)) (coeffs f) (length (coeffs f))" 
        unfolding d by auto
      also have "\<dots> = g * f" unfolding karatsuba_main by auto
      also have "\<dots> = ?rhs" by auto
      finally show ?thesis .
    next
      case False
      with outer have "?lhs = karatsuba_main (coeffs f) (length (coeffs f)) (coeffs g) (length (coeffs g))" 
        unfolding d by auto
      also have "\<dots> = ?rhs" unfolding karatsuba_main by auto
      finally show ?thesis .
    qed
  qed
qed

lemma karatsuba_mult_poly_code_unfold[code_unfold]: "(*) = karatsuba_mult_poly" 
  by (intro ext, unfold karatsuba_mult_poly, auto)

text \<open>The following declaration will resolve a race-conflict between @{thm karatsuba_mult_poly_code_unfold}
  and @{thm monom_mult_unfold}.\<close>
lemmas karatsuba_monom_mult_code_unfold[code_unfold] = 
  monom_mult_unfold[where f = "f :: 'a :: comm_ring_1 poly" for f, unfolded karatsuba_mult_poly_code_unfold]

end
