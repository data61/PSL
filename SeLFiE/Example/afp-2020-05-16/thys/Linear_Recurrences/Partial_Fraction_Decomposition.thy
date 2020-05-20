(*
  File:     Partial_Fraction_Decomposition.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>
  
  Partial fraction decomposition on Euclidean rings, i.e. decomposing a quotient into a 
  sum of quotients where each denominator is a power of an irreducible element. (and possibly 
  one summand that is an entire element)
  The most interesting setting is when the Euclidean ring is a polynomial ring.
*)
section \<open>Partial Fraction Decomposition\<close>
theory Partial_Fraction_Decomposition
imports 
  Main
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Library.Sublist"
  Linear_Recurrences_Misc
begin

subsection \<open>Decomposition on general Euclidean rings\<close>

text \<open>
  Consider elements $x, y_1, \ldots, y_n$ of a ring $R$, where the $y_i$ are pairwise coprime.
  A \emph{Partial Fraction Decomposition} of these elements (or rather the formal quotient 
  $x / (y_1 \ldots y_n)$ that they represent) is a finite sum of summands of the form 
  $a / y_i ^ k$. Obviously, the sum can be arranged such that there is at most one summand 
  with denominator $y_i ^ n$ for any combination of $i$ and $n$; in particular, there is at 
  most one summand with denominator 1.
  
  We can decompose the summands further by performing division with remainder until in all 
  quotients, the numerator's Euclidean size is less than that of the denominator.
\<close>


text \<open>
  The following function performs the first step of the above process: it takes the values 
  $x$ and $y_1,\ldots, y_n$ and returns the numerators of the summands in the decomposition. 
  (the denominators are simply the $y_i$ from the input)
\<close>
fun decompose :: "('a :: euclidean_ring_gcd) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "decompose x [] = []"
| "decompose x [y] = [x]"
| "decompose x (y#ys) = 
     (case bezout_coefficients y (prod_list ys) of
        (a, b) \<Rightarrow> (b*x) # decompose (a*x) ys)"

lemma decompose_rec:
  "ys \<noteq> [] \<Longrightarrow> decompose x (y#ys) = 
     (case bezout_coefficients y (prod_list ys) of 
        (a, b) \<Rightarrow> (b*x) # decompose (a*x) ys)"
  by (cases ys) simp_all

lemma length_decompose [simp]: "length (decompose x ys) = length ys"
proof (induction x ys rule: decompose.induct)
  case (3 x y z ys)
  obtain a b where ab: "(a,b) = bezout_coefficients y (prod_list (z#ys))"
    by (cases "bezout_coefficients y (z * prod_list ys)") simp_all
  from 3[OF ab] ab[symmetric] show ?case by simp
qed simp_all

fun decompose' :: "('a :: euclidean_ring_gcd) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "decompose' x [] _ = []"
| "decompose' x [y] _ = [x]"
| "decompose' _ _ [] = []"
| "decompose' x (y#ys) (p#ps) = 
     (case bezout_coefficients y p of
        (a, b) \<Rightarrow> (b*x) # decompose' (a*x) ys ps)"

primrec decompose_aux :: "'a :: {ab_semigroup_mult,monoid_mult} \<Rightarrow> _" where
  "decompose_aux acc [] = [acc]"
| "decompose_aux acc (x#xs) = acc # decompose_aux (x * acc) xs"

lemma decompose_code [code]:
  "decompose x ys = decompose' x ys (tl (rev (decompose_aux 1 (rev ys))))"
proof (induction x ys rule: decompose.induct)
  case (3 x y1 y2 ys)
  have [simp]: 
    "decompose_aux acc xs = map (\<lambda>x. prod_list x * acc) (prefixes xs)" for acc :: 'a and xs
    by (induction xs arbitrary: acc) (simp_all add: mult_ac)
  show ?case
    using 3[of "fst (bezout_coefficients y1 (y2 * prod_list ys))"
               "snd (bezout_coefficients y1 (y2 * prod_list ys))"]
    by (simp add: case_prod_unfold rev_map prefixes_conv_suffixes o_def mult_ac)
qed simp_all


text \<open>
  The next function performs the second step: Given a quotient of the form $x / y^n$, it 
  returns a list of $x_0, \ldots, x_n$ such that $x / y^n = x_0 / y^n + \ldots + x_{n-1} / y + x_n$
  and all $x_i$ have a Euclidean size less than that of $y$.
\<close>
fun normalise_decomp :: "('a :: semiring_modulo) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<times> ('a list)" where
  "normalise_decomp x y 0 = (x, [])"
| "normalise_decomp x y (Suc n) = (
     case normalise_decomp (x div y) y n of
       (z, rs) \<Rightarrow> (z, x mod y # rs))"

lemma length_normalise_decomp [simp]: "length (snd (normalise_decomp x y n)) = n"
  by (induction x y n rule: normalise_decomp.induct) (auto split: prod.split)

       

text \<open>
  The following constant implements the full process of partial fraction decomposition: 
  The input is a quotient $x / (y_1 ^ {k_1} \ldots y_n ^ {k_n})$ and the output is a sum of 
  an entire element and terms of the form $a / y_i ^ k$ where $a$ has a Euclidean size less 
  than $y_i$.
\<close>
definition partial_fraction_decomposition :: 
    "'a :: euclidean_ring_gcd \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'a \<times> 'a list list" where
  "partial_fraction_decomposition x ys = (if ys = [] then (x, []) else
     (let zs = [let (y, n) = ys ! i
                in  normalise_decomp (decompose x (map (\<lambda>(y,n). y ^ Suc n) ys) ! i) y (Suc n). 
                  i \<leftarrow> [0..<length ys]]
      in  (sum_list (map fst zs), map snd zs)))"
      
lemma length_pfd1 [simp]:
  "length (snd (partial_fraction_decomposition x ys)) = length ys"
  by (simp add: partial_fraction_decomposition_def)

lemma length_pfd2 [simp]:
  "i < length ys \<Longrightarrow> length (snd (partial_fraction_decomposition x ys) ! i) = snd (ys ! i) + 1"
  by (auto simp: partial_fraction_decomposition_def case_prod_unfold Let_def)

lemma size_normalise_decomp:
  "a \<in> set (snd (normalise_decomp x y n)) \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> euclidean_size a < euclidean_size y"
  by (induction x y n rule: normalise_decomp.induct)
     (auto simp: case_prod_unfold Let_def mod_size_less)

lemma size_partial_fraction_decomposition:
 "i < length xs \<Longrightarrow> fst (xs ! i) \<noteq> 0 \<Longrightarrow> x \<in> set (snd (partial_fraction_decomposition y xs) ! i)
    \<Longrightarrow> euclidean_size x < euclidean_size (fst (xs ! i))"
 by (auto simp: partial_fraction_decomposition_def Let_def case_prod_unfold
          simp del: normalise_decomp.simps split: if_split_asm intro!: size_normalise_decomp)  


text \<open>
  A homomorphism $\varphi$ from a Euclidean ring $R$ into another ring $S$ with a notion of 
  division. We will show that for any $x,y\in R$ such that $\phi(y)$ is a unit, we can perform 
  partial fraction decomposition on the quotient $\varphi(x) / \varphi(y)$.
  
  The obvious choice for $S$ is the fraction field of $R$, but other choices may also make sense: 
  If, for example, $R$ is a ring of polynomials $K[X]$, then one could let $S = K$ and $\varphi$ 
  the evaluation homomorphism. Or one could let $S = K[[X]]$ (the ring of formal power series) and 
  $\varphi$ the canonical homomorphism from polynomials to formal power series.
\<close>

locale pfd_homomorphism =
fixes lift :: "('a :: euclidean_ring_gcd) \<Rightarrow> ('b :: euclidean_semiring_cancel)"
assumes lift_add: "lift (a + b) = lift a + lift b"                   
assumes lift_mult: "lift (a * b) = lift a * lift b"
assumes lift_0 [simp]: "lift 0 = 0"
assumes lift_1 [simp]: "lift 1 = 1"
begin

lemma lift_power:
  "lift (a ^ n) = lift a ^ n"
  by (induction n) (simp_all add: lift_mult)

definition from_decomp :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'b" where
  "from_decomp x y n = lift x div lift y ^ n"

lemma decompose:
  assumes "ys \<noteq> []" "pairwise coprime (set ys)" "distinct ys"
          "\<And>y. y \<in> set ys \<Longrightarrow> is_unit (lift y)"
  shows   "(\<Sum>i<length ys. lift (decompose x ys ! i) div lift (ys ! i)) = 
             lift x div lift (prod_list ys)"
  using assms
proof (induction ys arbitrary: x rule: list_nonempty_induct)
  case (cons y ys x)
  from cons.prems have "coprime (prod_list ys) y"
    by (auto simp add: pairwise_insert intro: prod_list_coprime_left)
  from cons.prems have unit: "is_unit (lift y)" by simp
  moreover from cons.prems have "\<forall>y\<in>set ys. is_unit (lift y)" by simp
  hence unit': "is_unit (lift (prod_list ys))" by (induction ys) (auto simp: lift_mult)
  ultimately have unit: "lift y dvd b" "lift (prod_list ys) dvd b" for b by auto
  
  obtain s t where st: "bezout_coefficients y (prod_list ys) = (s, t)"
    by (cases "bezout_coefficients y (prod_list ys)") simp_all

  from \<open>pairwise coprime (set (y#ys))\<close> 
  have  coprime:"pairwise coprime (set ys)"
    by (rule pairwise_subset) auto

  have "(\<Sum>i<length (y # ys). lift (decompose x (y # ys) ! i) div lift ((y # ys) ! i)) = 
          lift (t * x) div lift y + lift (s * x) div lift (prod_list ys)"
    using cons.hyps cons.prems coprime unfolding length_Cons atLeast0LessThan [symmetric]
    by (subst sum.atLeast_Suc_lessThan, simp, subst sum.shift_bounds_Suc_ivl)
       (simp add: atLeast0LessThan decompose_rec st cons.IH lift_mult)
  also have "(lift (t * x) div lift y + lift (s * x) div lift (prod_list ys)) *
                lift (prod_list (y#ys)) = 
             lift (prod_list ys) * (lift y * (lift (t * x) div lift y)) + 
             lift y * (lift (prod_list ys) * (lift (s * x) div lift (prod_list ys)))"
                by (simp_all add: lift_mult algebra_simps)
  also have "\<dots> = lift (prod_list ys * t * x + y * s * x)" using assms unit 
    by (simp add: lift_mult lift_add algebra_simps)
  finally have "(\<Sum>i<length (y # ys). lift (decompose x (y # ys) ! i) div lift ((y # ys) ! i)) =
                  lift ((s * y + t * prod_list ys) * x) div lift (prod_list (y#ys))"
    using unit by (subst unit_eq_div2) (auto simp: lift_mult lift_add algebra_simps)
  also have "s * y + t * prod_list ys = gcd (prod_list ys) y"
    using bezout_coefficients_fst_snd[of y "prod_list ys"] by (simp add: st gcd.commute)
  also have "\<dots> = 1"
    using \<open>coprime (prod_list ys) y\<close> by simp
  finally show ?case by simp
qed simp_all

lemma normalise_decomp:
  fixes x y :: 'a and n :: nat
  assumes "is_unit (lift y)"
  defines "xs \<equiv> snd (normalise_decomp x y n)"
  shows   "lift (fst (normalise_decomp x y n)) + (\<Sum>i<n. from_decomp (xs!i) y (n-i)) =
             lift x div lift y ^ n"
using assms unfolding xs_def
proof (induction x y n rule: normalise_decomp.induct, goal_cases)
  case (2 x y n)
  from 2(2) have unit: "is_unit (lift y ^ n)" 
    by (simp add: is_unit_power_iff)
  obtain a b where ab: "normalise_decomp (x div y) y n = (a, b)" 
    by (cases "normalise_decomp (x div y) y n") simp_all
  have "lift (fst (normalise_decomp x y (Suc n))) + 
            (\<Sum>i<Suc n. from_decomp (snd (normalise_decomp x y (Suc n)) ! i) y (Suc n - i)) =
          lift a + (\<Sum>i<n. from_decomp (b ! i) y (n - i)) + from_decomp (x mod y) y (Suc n)"
    unfolding atLeast0LessThan[symmetric]
    apply (subst sum.atLeast_Suc_lessThan)
    apply simp
    apply (subst sum.shift_bounds_Suc_ivl)
    apply (simp add: ab atLeast0LessThan ac_simps)
    done
  also have "lift a + (\<Sum>i<n. from_decomp (b ! i) y (n - i)) = 
               lift (x div y) div lift y ^ n"
    using 2 by (simp add: ab)
  also from 2(2) unit have "(\<dots> + from_decomp (x mod y) y (Suc n)) * lift y = 
      (lift ((x div y) * y + x mod y) div lift y ^ n)" (is "?A * _ = ?B div _")
      unfolding lift_add lift_mult
      apply (subst div_add)
      apply (auto simp add: from_decomp_def algebra_simps dvd_div_mult2_eq 
        unit_div_mult_swap dvd_div_mult2_eq[OF unit_imp_dvd] is_unit_mult_iff)
      done
  with 2(2) have "?A = \<dots> div lift y" by (subst eq_commute, subst dvd_div_eq_mult) auto
  also from 2(2) unit have "\<dots> = ?B div (lift y ^ Suc n)"
    by (subst is_unit_div_mult2_eq [symmetric]) (auto simp: mult_ac)
  also have "x div y * y + x mod y = x" by (rule div_mult_mod_eq)
  finally show ?case .
qed simp_all
     
lemma lift_prod_list: "lift (prod_list xs) = prod_list (map lift xs)"
  by (induction xs) (simp_all add: lift_mult)

lemma lift_sum: "lift (sum f A) = sum (\<lambda>x. lift (f x)) A"
  by (cases "finite A", induction A rule: finite_induct) (simp_all add: lift_add)
  
lemma partial_fraction_decomposition:
  fixes   ys :: "('a \<times> nat) list"
  defines "ys' \<equiv> map (\<lambda>(x,n). x ^ Suc n) ys :: 'a list"
  assumes unit: "\<And>y. y \<in> fst ` set ys \<Longrightarrow> is_unit (lift y)" 
  assumes coprime: "pairwise coprime (set ys')"
  assumes distinct: "distinct ys'"
  assumes "partial_fraction_decomposition x ys = (a, zs)"
  shows   "lift a + (\<Sum>i<length ys. \<Sum>j\<le>snd (ys!i). 
                       from_decomp (zs!i!j) (fst (ys!i)) (snd (ys!i)+1 - j)) = 
             lift x div lift (prod_list ys')" 
proof (cases "ys = []")
  assume [simp]: "ys \<noteq> []"
  define n where "n = length ys"

  have "lift x div lift (prod_list ys') = (\<Sum>i<n. lift (decompose x ys' ! i) div lift (ys' ! i))"
    using assms by (subst decompose [symmetric])
      (force simp: lift_prod_list prod_list_zero_iff lift_power lift_mult o_def n_def 
        is_unit_mult_iff is_unit_power_iff)+ 
  also have "\<dots> = 
    (\<Sum>i<n. lift (fst (normalise_decomp (decompose x ys' ! i) (fst (ys!i)) (snd (ys!i)+1)))) +
    (\<Sum>i<n. (\<Sum>j\<le>snd (ys!i). from_decomp (zs!i!j) (fst (ys!i)) (snd (ys!i)+1 - j)))" (is "_ = ?A + ?B")
  proof (subst sum.distrib [symmetric], intro sum.cong refl, goal_cases)
    case (1 i)
    from 1 have "lift (ys' ! i) = lift (fst (ys ! i)) ^ Suc (snd (ys ! i))"
      by (simp add: ys'_def n_def lift_power lift_mult split: prod.split)
    also from 1 have "lift (decompose x ys' ! i) div \<dots> = 
      lift (fst (normalise_decomp (decompose x ys' ! i) (fst (ys!i)) (snd (ys!i)+1))) +
      (\<Sum>j<Suc (snd (ys ! i)). from_decomp (snd (normalise_decomp (decompose x ys' ! i)
             (fst (ys!i)) (snd (ys!i)+1)) ! j) (fst (ys ! i)) (snd (ys!i)+1 - j))" (is "_ = _ + ?C")
      by (subst normalise_decomp [symmetric]) (simp_all add: n_def unit)
    also have "?C = (\<Sum>j\<le>snd (ys!i). from_decomp (zs!i!j) (fst (ys!i)) (snd (ys!i)+1 - j))"
      using assms 1
      by (intro sum.cong refl)
         (auto simp: partial_fraction_decomposition_def case_prod_unfold Let_def o_def n_def
               simp del: normalise_decomp.simps)
     finally show ?case .
  qed
  also from assms have "?A = lift a"
    by (auto simp: partial_fraction_decomposition_def o_def sum_list_sum_nth atLeast0LessThan
                   case_prod_unfold Let_def lift_sum n_def intro!: sum.cong)  
  finally show ?thesis by (simp add: n_def)
qed (insert assms, simp add: partial_fraction_decomposition_def)

end


subsection \<open>Specific results for polynomials\<close>

definition divmod_field_poly :: "'a :: field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "divmod_field_poly p q = (p div q, p mod q)"
  
lemma divmod_field_poly_code [code]:
  "divmod_field_poly p q =
   (let cg = coeffs q
    in if cg = [] then (0, p)
       else let cf = coeffs p; ilc = inverse (last cg);
                ch = map ((*) ilc) cg;
                (q, r) =
                  divmod_poly_one_main_list [] (rev cf) (rev ch)
                  (1 + length cf - length cg)
            in (poly_of_list (map ((*) ilc) q), poly_of_list (rev r)))"
  unfolding divmod_field_poly_def by (rule pdivmod_via_divmod_list)

definition normalise_decomp_poly :: "'a::field_gcd poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly list" 
  where [simp]: "normalise_decomp_poly (p :: _ poly) q n = normalise_decomp p q n"

lemma normalise_decomp_poly_code [code]:
  "normalise_decomp_poly x y 0 = (x, [])"
  "normalise_decomp_poly x y (Suc n) = (
     let (x', r) = divmod_field_poly x y;
         (z, rs) = normalise_decomp_poly x' y n
     in  (z, r # rs))"
  by (simp_all add: divmod_field_poly_def)

definition poly_pfd_simple where
  "poly_pfd_simple x cs = (if cs = [] then (x, []) else
     (let zs = [let (c, n) = cs ! i
                in  normalise_decomp_poly (decompose x 
                      (map (\<lambda>(c,n). [:1,-c:] ^ Suc n) cs) ! i) [:1,-c:] (n+1). 
                i \<leftarrow> [0..<length cs]]
      in  (sum_list (map fst zs), map (map (\<lambda>p. coeff p 0) \<circ> snd) zs)))"
      
lemma poly_pfd_simple_code [code]:
  "poly_pfd_simple x cs = 
    (if cs = [] then (x, []) else
       let zs = zip_with (\<lambda>(c,n) decomp. normalise_decomp_poly decomp [:1,-c:] (n+1))
                  cs (decompose x (map (\<lambda>(c,n). [:1,-c:] ^ Suc n) cs))
      in  (sum_list (map fst zs), map (map (\<lambda>p. coeff p 0) \<circ> snd) zs))"
  unfolding poly_pfd_simple_def zip_with_altdef'
  by (simp add: Let_def case_prod_unfold)

lemma fst_poly_pfd_simple: 
  "fst (poly_pfd_simple x cs) = 
      fst (partial_fraction_decomposition x (map (\<lambda>(c,n). ([:1,-c:],n)) cs))"
  by (auto simp: poly_pfd_simple_def partial_fraction_decomposition_def o_def
             case_prod_unfold Let_def sum_list_sum_nth intro!: sum.cong)

lemma const_polyI: "degree p = 0 \<Longrightarrow> [:coeff p 0:] = p"
  by (elim degree_eq_zeroE) simp_all
  
lemma snd_poly_pfd_simple:
  "map (map (\<lambda>c. [:c :: 'a :: field_gcd:])) (snd (poly_pfd_simple x cs)) = 
      (snd (partial_fraction_decomposition x (map (\<lambda>(c,n). ([:1,-c:],n)) cs)))"
proof -
  have "snd (poly_pfd_simple x cs) = map (map (\<lambda>p. coeff p 0))
          (snd (partial_fraction_decomposition x (map (\<lambda>(c,n). ([:1,-c:],n)) cs)))"
       (is "_ = map ?f ?B")
    by (auto simp: poly_pfd_simple_def partial_fraction_decomposition_def o_def
               case_prod_unfold Let_def sum_list_sum_nth intro!: sum.cong)
  also have "map (map (\<lambda>c. [:c:])) (map ?f ?B) = map (map (\<lambda>x. x)) ?B"
    unfolding map_map o_def
  proof (intro map_cong refl const_polyI, goal_cases)
    case (1 ys y)
    from 1 obtain i where i: "i < length cs"
      "ys = snd (partial_fraction_decomposition x (map (\<lambda>(c,n). ([:1,-c:],n)) cs)) ! i"
      by (auto simp: in_set_conv_nth)
    with 1 have "euclidean_size y < euclidean_size (fst (map (\<lambda>(c,n). ([:1,-c:],n)) cs ! i))"
      by (intro size_partial_fraction_decomposition[of i _ _ x])
         (auto simp: case_prod_unfold Let_def)
    with i(1) have "euclidean_size y < 2" 
      by (auto simp: case_prod_unfold Let_def euclidean_size_poly_def split: if_split_asm)
    thus ?case
      by (cases y rule: pCons_cases) (auto simp: euclidean_size_poly_def split: if_split_asm)
  qed
  finally show ?thesis by simp
qed

lemma poly_pfd_simple:
  "partial_fraction_decomposition x (map (\<lambda>(c,n). ([:1,-c:],n)) cs) =
         (fst (poly_pfd_simple x cs), map (map (\<lambda>c. [:c:])) (snd (poly_pfd_simple x cs)))"
  by (simp add: fst_poly_pfd_simple snd_poly_pfd_simple)

end
