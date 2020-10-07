section \<open>Subresultants and the subresultant PRS\<close>

text \<open>This theory contains most of the soundness proofs of the subresultant PRS algorithm,
  where we closely follow the papers of Brown \cite{Brown} and Brown and Traub \cite{BrownTraub}.
  This is in contrast to a similar Coq formalization of Mahboubi \cite{Mahboubi06} which
  is based on polynomial determinants.

  Whereas the current file only contains an algorithm to compute the resultant of two polynomials
  efficiently, there is another theory ``Subresultant-Gcd'' which also contains the algorithm
  to compute the GCD of two polynomials via the subresultant algorithm. In both algorithms we
  integrate Lazard's optimization in the dichotomous version,
  but not the second optmization described by Ducos \cite{Ducos}.\<close>
theory Subresultant
imports
  Resultant_Prelim
  Dichotomous_Lazard
  Binary_Exponentiation
  More_Homomorphisms
  Coeff_Int
begin

subsection \<open>Algorithm\<close>

context
  fixes div_exp :: "'a :: idom_divide \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
begin
partial_function(tailrec) subresultant_prs_main where
  "subresultant_prs_main f g c = (let
   m = degree f;
   n = degree g;
   lf = lead_coeff f;
   lg = lead_coeff g;
   \<delta> = m - n;
   d = div_exp lg c \<delta>;
   h = pseudo_mod f g
  in if h = 0 then (g,d)
     else subresultant_prs_main g (sdiv_poly h ((-1) ^ (\<delta> + 1) * lf * (c ^ \<delta>))) d)"

definition subresultant_prs where
  [code del]: "subresultant_prs f g = (let
    h = pseudo_mod f g;
    \<delta> = (degree f - degree g);
    d = lead_coeff g ^ \<delta>
    in if h = 0 then (g,d)
       else subresultant_prs_main g ((- 1) ^ (\<delta> + 1) * h) d)"

definition resultant_impl_main where
  [code del]: "resultant_impl_main G1 G2 = (if G2 = 0 then (if degree G1 = 0 then 1 else 0) else
     case subresultant_prs G1 G2 of
     (Gk,hk) \<Rightarrow> (if degree Gk = 0 then hk else 0))"

definition resultant_impl_generic where
  "resultant_impl_generic f g =
     (if length (coeffs f) \<ge> length (coeffs g) then resultant_impl_main f g
     else let res = resultant_impl_main g f in
      if even (degree f) \<or> even (degree g) then res else - res)"
end

definition basic_div_exp :: "'a :: idom_divide \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "basic_div_exp x y n = x^n div y^(n-1)"

text \<open>Using @{const basic_div_exp} we obtain a more generic implementation, which is however
  less efficient. It is currently not further developed, except for getting the raw soundness statement.\<close>
definition resultant_impl_idom_divide :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: idom_divide" where
  "resultant_impl_idom_divide = resultant_impl_generic basic_div_exp"

text \<open>The default variant uses the optimized computation @{const dichotomous_Lazard}.
  For this variant, later on optimized code-equations are proven.
  However, the implementation restricts to sort @{class factorial_ring_gcd}.\<close>
definition resultant_impl :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: factorial_ring_gcd" where
  [code del]: "resultant_impl = resultant_impl_generic dichotomous_Lazard"

subsection \<open>Soundness Proof for @{term "resultant_impl = resultant"}\<close>

lemma basic_div_exp: assumes "(to_fract x)^n / (to_fract y)^(n-1) \<in> range to_fract"
  shows "to_fract (basic_div_exp x y n) = (to_fract x)^n / (to_fract y)^(n-1)"
  unfolding basic_div_exp_def by (rule sym, rule div_divide_to_fract[OF assms refl refl], auto simp: hom_distribs)

abbreviation pdivmod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly"
where
  "pdivmod p q \<equiv> (p div q, p mod q)"

lemma even_sum_list: assumes "\<And> x. x \<in> set xs \<Longrightarrow> even (f x) = even (g x)"
  shows "even (sum_list (map f xs)) = even (sum_list (map g xs))"
  using assms by (induct xs, auto)

lemma for_all_Suc: "P i \<Longrightarrow> (\<forall> j \<ge> Suc i. P j) = (\<forall> j \<ge> i. P j)" for P
  by (metis (full_types) Suc_le_eq less_le)

(* part on pseudo_divmod *)
lemma pseudo_mod_left_0[simp]: "pseudo_mod 0 x = 0"
  unfolding pseudo_mod_def pseudo_divmod_def
  by (cases "x = 0"; cases "length (coeffs x)", auto)

lemma pseudo_mod_right_0[simp]: "pseudo_mod x 0 = x"
  unfolding pseudo_mod_def pseudo_divmod_def by simp

lemma snd_pseudo_divmod_main_cong:
  assumes "a1 = b1" "a3 = b3" "a4 = b4" "a5 = b5" "a6 = b6" (* note that a2 = b2 is not required! *)
  shows "snd (pseudo_divmod_main a1 a2 a3 a4 a5 a6) = snd (pseudo_divmod_main b1 b2 b3 b4 b5 b6)"
using assms snd_pseudo_divmod_main by metis

lemma snd_pseudo_mod_smult_invar_right:
  shows "(snd (pseudo_divmod_main (x * lc) q r (smult x d) dr n))
         = snd (pseudo_divmod_main lc q' (smult (x^n) r) d dr n)"
proof(induct n arbitrary: q q' r dr)
  case (Suc n)
  let ?q = "smult (x * lc) q + monom (coeff r dr) n"
  let ?r = "smult (x * lc) r - (smult x (monom (coeff r dr) n * d))"
  let ?dr = "dr - 1"
  let ?rec_lhs = "pseudo_divmod_main (x * lc) ?q ?r (smult x d) ?dr n"
  let ?rec_rhs = "pseudo_divmod_main lc q' (smult (x^n) ?r) d ?dr n"
  have [simp]: "\<And> n. x ^ n * (x * lc) = lc * (x * x ^ n)"
               "\<And> n c. x ^ n * (x * c) = x * x ^ n * c"
               "\<And> n. x * x ^ n * lc = lc * (x * x ^ n)"
    by (auto simp: ac_simps)
  have "snd (pseudo_divmod_main (x * lc) q r (smult x d) dr (Suc n)) = snd ?rec_lhs"
    by (auto simp:Let_def)
  also have "\<dots> = snd ?rec_rhs" using Suc by auto
  also have "\<dots> = snd (pseudo_divmod_main lc q' (smult (x^Suc n) r) d dr (Suc n))"
    unfolding pseudo_divmod_main.simps Let_def
    proof(rule snd_pseudo_divmod_main_cong,goal_cases)
      case 2
      show ?case by (auto simp:smult_add_right smult_diff_right smult_monom smult_monom_mult)
    qed auto
  finally show ?case by auto
qed auto

lemma snd_pseudo_mod_smult_invar_left:
  shows "snd (pseudo_divmod_main lc q (smult x r) d dr n)
       = smult x (snd (pseudo_divmod_main lc q' r d dr n))"
proof(induct n arbitrary:x lc q q' r d dr)
  case (Suc n)
  have sm:"smult lc (smult x r) - monom (coeff (smult x r) dr) n * d
          =smult x (smult lc r - monom (coeff r dr) n * d) "
    by (auto simp:smult_diff_right smult_monom smult_monom_mult mult.commute[of lc x])
  let ?q' = "smult lc q' + monom (coeff r dr) n"
  show ?case unfolding pseudo_divmod_main.simps Let_def Suc(1)[of lc _ _ _ _ _ ?q'] sm by auto
qed auto

lemma snd_pseudo_mod_smult_left[simp]:
  shows "snd (pseudo_divmod (smult (x::'a::idom) p) q) = (smult x (snd (pseudo_divmod p q)))"
  unfolding pseudo_divmod_def
    by (auto simp:snd_pseudo_mod_smult_invar_left[of _ _ _ _ _ _ _ 0] Polynomial.coeffs_smult)

lemma pseudo_mod_smult_right:
  assumes "(x::'a::idom)\<noteq>0" "q\<noteq>0"
  shows "(pseudo_mod p (smult (x::'a::idom) q)) = (smult (x^(Suc (length (coeffs p)) - length (coeffs q))) (pseudo_mod p q))"
  unfolding pseudo_divmod_def pseudo_mod_def
    by (auto simp:snd_pseudo_mod_smult_invar_right[of _ _ _ _ _ _ _ 0]
                  snd_pseudo_mod_smult_invar_left[of _ _ _ _ _ _ _ 0] Polynomial.coeffs_smult assms)

lemma pseudo_mod_zero[simp]:
"pseudo_mod 0 f = (0::'a :: {idom} poly)"
"pseudo_mod f 0 = f"
unfolding pseudo_mod_def snd_pseudo_mod_smult_left[of 0 _ f,simplified]
unfolding pseudo_divmod_def by auto

(* part on prod_list *)

lemma prod_combine:
  assumes "j \<le> i"
  shows "f i * (\<Prod>l\<leftarrow>[j..<i]. (f l :: 'a::comm_monoid_mult)) = prod_list (map f [j..<Suc i])"
proof(subst prod_list_map_remove1[of i "[j..<Suc i]" f],goal_cases)
  case 2
  have "remove1 i ([j..<i] @ [i]) = [j..<i]" by (simp add: remove1_append)
  thus ?case by auto
qed (insert assms, auto)

lemma prod_list_minus_1_exp: "prod_list (map (\<lambda> i. (-1)^(f i)) xs)
  = (-1)^(sum_list (map f xs))"
  by (induct xs, auto simp: power_add)

lemma minus_1_power_even: "(- (1 :: 'b :: comm_ring_1))^ k = (if even k then 1 else (-1))"
  by auto

lemma minus_1_even_eqI: assumes "even k = even l" shows
    "(- (1 :: 'b :: comm_ring_1))^k = (- 1)^l"
    unfolding minus_1_power_even assms by auto

lemma (in comm_monoid_mult) prod_list_multf:
  "(\<Prod>x\<leftarrow>xs. f x * g x) = prod_list (map f xs) * prod_list (map g xs)"
  by (induct xs) (simp_all add: algebra_simps)

lemma inverse_prod_list: "inverse (prod_list xs) = prod_list (map inverse (xs :: 'a :: field list))"
  by (induct xs, auto)

(* part on pow_int, i.e., exponentiation with integer exponent *)
definition pow_int :: "'a :: field \<Rightarrow> int \<Rightarrow> 'a" where
  "pow_int x e = (if e < 0 then 1 / (x ^ (nat (-e))) else x ^ (nat e))"

lemma pow_int_0[simp]: "pow_int x 0 = 1" unfolding pow_int_def by auto

lemma pow_int_1[simp]: "pow_int x 1 = x" unfolding pow_int_def by auto

lemma exp_pow_int: "x ^ n = pow_int x n"
  unfolding pow_int_def by auto

lemma pow_int_add: assumes x: "x \<noteq> 0" shows "pow_int x (a + b) = pow_int x a * pow_int x b"
proof -
  have *:
    "\<not> a + b < 0 \<Longrightarrow> a < 0 \<Longrightarrow> nat b = nat (a + b) + nat (-a)"
    "\<not> a + b < 0 \<Longrightarrow> b < 0 \<Longrightarrow> nat a = nat (a + b) + nat (-b)"
    "a + b < 0 \<Longrightarrow> \<not> a < 0 \<Longrightarrow> nat (-b) = nat a + nat (-a -b) "
    "a + b < 0 \<Longrightarrow> \<not> b < 0 \<Longrightarrow> nat (-a) = nat b + nat (-a -b) "
  by auto
  have pow_eq: "l = m \<Longrightarrow> (x ^ l = x ^ m)" for l m by auto
  from x show ?thesis unfolding pow_int_def
    by (auto split: if_splits simp: power_add[symmetric] simp: * intro!: pow_eq, auto simp: power_add)
qed

lemma pow_int_mult: "pow_int (x * y) a = pow_int x a * pow_int y a"
  unfolding pow_int_def by (cases "a < 0", auto simp: power_mult_distrib)

lemma pow_int_base_1[simp]: "pow_int 1 a = 1"
  unfolding pow_int_def by (cases "a < 0", auto)

lemma pow_int_divide: "a / pow_int x b = a * pow_int x (-b)"
  unfolding pow_int_def by (cases b rule: linorder_cases[of _ 0], auto)

lemma divide_prod_assoc: "x / (y * z :: 'a :: field) = x / y / z" by (simp add: field_simps)

lemma minus_1_inverse_pow[simp]: "x / (-1)^n = (x :: 'a :: field) * (-1)^n"
  by (simp add: minus_1_power_even)

(* part on subresultants *)
definition subresultant_mat :: "nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly mat" where
  "subresultant_mat J F G = (let
     dg = degree G; df = degree F; f = coeff_int F; g = coeff_int G; n = (df - J) + (dg - J)
     in mat n n (\<lambda> (i,j). if j < dg - J then
       if i = n - 1 then monom 1 (dg - J - 1 - j) * F else [: f (df - int i + int j) :]
      else let jj = j - (dg - J) in
       if i = n - 1 then monom 1 (df - J - 1 - jj) * G else [: g (dg - int i + int jj) :]))"

lemma subresultant_mat_dim[simp]:
  fixes j p q
  defines "S \<equiv> subresultant_mat j p q"
  shows "dim_row S = (degree p - j) + (degree q - j)" and "dim_col S = (degree p - j) + (degree q - j)"
  unfolding S_def subresultant_mat_def Let_def by auto

definition subresultant'_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a mat" where
  "subresultant'_mat J l F G = (let
     \<gamma> = degree G; \<phi> = degree F; f = coeff_int F; g = coeff_int G; n = (\<phi> - J) + (\<gamma> - J)
     in mat n n (\<lambda> (i,j). if j < \<gamma> - J then
       if i = n - 1 then (f (l - int (\<gamma> - J - 1) + int j)) else (f (\<phi> - int i + int j))
      else let jj = j - (\<gamma> - J) in
       if i = n - 1 then (g (l - int (\<phi> - J - 1) + int jj)) else (g (\<gamma> - int i + int jj))))"

lemma subresultant_index_mat:
  fixes F G
  assumes i: "i < (degree F - J) + (degree G - J)" and j: "j < (degree F - J) + (degree G - J)"
  shows "subresultant_mat J F G $$ (i,j) =
    (if j < degree G - J then
       if i = (degree F - J) + (degree G - J) - 1 then monom 1 (degree G - J - 1 - j) * F else ([: coeff_int F ( degree F - int i + int j) :])
      else let jj = j - (degree G - J) in
       if i = (degree F - J) + (degree G - J) - 1 then monom 1 ( degree F - J - 1 - jj) * G else ([: coeff_int G (degree G - int i + int jj) :]))"
  unfolding subresultant_mat_def Let_def
  unfolding index_mat(1)[OF i j] split by auto

definition subresultant :: "nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "subresultant J F G = det (subresultant_mat J F G)"


lemma subresultant_smult_left: assumes "(c :: 'a :: {comm_ring_1, semiring_no_zero_divisors}) \<noteq> 0"
  shows "subresultant J (smult c f) g = smult (c ^ (degree g - J)) (subresultant J f g)"
proof -
  let ?df = "degree f"
  let ?dg = "degree g"
  let ?n = "(?df - J) + (?dg - J)"
  let ?m = "?dg - J"
  let ?M = "mat ?n ?n (\<lambda> (i,j). if i = j then if i < ?m then [:c:] else 1 else 0)"
  from \<open>c \<noteq> 0\<close> have deg: "degree (smult c f) = ?df" by simp
  let ?S = "subresultant_mat J f g"
  let ?cS = "subresultant_mat J (smult c f) g"
  have dim: "dim_row ?S = ?n" "dim_col ?S = ?n"  "dim_row ?cS = ?n" "dim_col ?cS = ?n" using deg by auto
  hence C: "?S \<in> carrier_mat ?n ?n" "?cS \<in> carrier_mat ?n ?n" "?M \<in> carrier_mat ?n ?n" by auto
  have dim': "dim_row (?S * ?M) = ?n" "dim_col (?S * ?M) = ?n" using dim (1,2) by simp_all
  define S where "S = ?S"
  have "?cS = ?S * ?M"
  proof (rule eq_matI, unfold dim' dim)
    fix i j
    assume ij: "i < ?n" "j < ?n"
    have "(?S * ?M) $$ (i,j) = row ?S i \<bullet> col ?M j"
      by (rule index_mult_mat, insert ij dim, auto)
    also have "\<dots> = (\<Sum>k = 0..<?n. row S i $ k * col ?M j $ k)" unfolding scalar_prod_def S_def[symmetric]
      by simp
    also have "\<dots> = (\<Sum>k = 0..<?n. S $$ (i,k) * ?M $$ (k,j))"
      by (rule sum.cong, insert ij, auto simp: S_def)
    also have "\<dots> = S $$ (i,j) * ?M $$ (j,j) + sum (\<lambda> k. S $$ (i,k) * ?M $$ (k,j)) ({0..<?n} - {j})"
      by (rule sum.remove, insert ij, auto)
    also have "\<dots> = S $$ (i,j) * ?M $$ (j,j)"
      by (subst sum.neutral, insert ij, auto)
    also have "\<dots> = ?cS $$ (i,j)" unfolding subresultant_index_mat[OF ij] S_def
      by (subst subresultant_index_mat, unfold deg, insert ij, auto)
    finally show "?cS $$ (i,j) = (?S * ?M) $$ (i,j)" by simp
  qed auto
  from arg_cong[OF this, of det] det_mult[OF C(1) C(3)]
  have "subresultant J (smult c f) g = subresultant J f g * det ?M"
    unfolding subresultant_def by auto
  also have "det ?M = [:c ^ ?m :]"
  proof (subst det_upper_triangular[OF _ C(3)])
    show "upper_triangular ?M"
      by (rule upper_triangularI, auto)
    have "prod_list (diag_mat ?M) = (\<Prod>k = 0..<?n. (?M $$ (k,k)))"
      unfolding prod_list_diag_prod by simp
    also have "\<dots> = (\<Prod>k = 0..<?m. ?M $$ (k,k)) * (\<Prod>k = ?m..<?n. ?M $$ (k,k))"
      by (subst prod.union_disjoint[symmetric], (auto)[3], rule prod.cong, auto)
    also have "(\<Prod>k = 0..<?m. ?M $$ (k,k)) = (\<Prod>k = 0..<?m. [: c :])"
      by (rule prod.cong, auto)
    also have "(\<Prod>k = 0..<?m. [: c :]) = [: c :] ^ ?m" by simp
    also have "(\<Prod>k = ?m..<?n. ?M $$ (k,k)) = (\<Prod>k = ?m..<?n. 1)"
      by (rule prod.cong, auto)
    finally show "prod_list (diag_mat ?M) = [: c^?m :]" unfolding poly_const_pow by simp
  qed
  finally show ?thesis by simp
qed

lemma subresultant_swap:
  shows "subresultant J f g = smult ((- 1) ^ ((degree f - J) * (degree g - J))) (subresultant J g f)"
proof -
  let ?A = "subresultant_mat J f g"
  let ?k = "degree f - J"
  let ?n = "degree g - J"
  have nk: "?n + ?k = ?k + ?n" by simp
  have change: "j < degree f - J + (degree g - J) \<Longrightarrow> ((if j < degree f - J then j + (degree g - J) else j - (degree f - J)) < degree g - J)
    = (\<not> (j < degree f - J))" for j by auto
  have "subresultant J f g = det ?A" unfolding subresultant_def by simp
  also have "\<dots> = (-1)^(?k * ?n) * det (mat (?k + ?n) (?k + ?n) (\<lambda> (i,j).
    ?A $$ (i,(if j < ?k then j + ?n else j - ?k))))" (is "_ = _ * det ?B")
    by (rule det_swap_cols, auto simp: subresultant_mat_def Let_def)
  also have "?B = subresultant_mat J g f"
    unfolding subresultant_mat_def Let_def
    by (rule eq_matI, unfold dim_row_mat dim_col_mat nk index_mat split,
      subst index_mat, (auto)[2], unfold split, subst change, force,
      unfold if_conn, rule if_cong[OF refl if_cong if_cong], auto)
  also have "det \<dots> = subresultant J g f" unfolding subresultant_def ..
  also have "(-1)^(?k * ?n) * \<dots> = [: (-1)^(?k * ?n) :] * \<dots> " by (unfold hom_distribs, simp)
  also have "\<dots> = smult ((-1)^(?k * ?n)) (subresultant J g f)" by simp
  finally show ?thesis .
qed

lemma subresultant_smult_right:assumes "(c :: 'a :: {comm_ring_1, semiring_no_zero_divisors}) \<noteq> 0"
  shows "subresultant J f (smult c g) = smult (c ^ (degree f - J)) (subresultant J f g)"
  unfolding subresultant_swap[of _ f] subresultant_smult_left[OF assms]
    degree_smult_eq using assms by (simp add: ac_simps)

lemma coeff_subresultant: "coeff (subresultant J F G) l =
  (if degree F - J + (degree G - J) = 0 \<and> l \<noteq> 0 then 0 else det (subresultant'_mat J l F G))"
proof (cases "degree F - J + (degree G - J) = 0")
  case True
  show ?thesis unfolding subresultant_def subresultant_mat_def subresultant'_mat_def Let_def True
    by simp
next
  case False
  let ?n = "degree F - J + (degree G - J)"
  define n where "n = ?n"
  from False have n: "n \<noteq> 0" unfolding n_def by auto
  hence id: "{0..<n} = insert (n - 1) {0..< (n - 1)}" by (cases n, auto)
  have idn: "(x = x) = True" for x :: nat by simp
  let ?M = "subresultant_mat J F G"
  define M where "M = ?M"
  let ?L = "subresultant'_mat J l F G"
  define L where "L = ?L"
  {
    fix p
    assume p: "p permutes {0..<n}"
    from n p have n1: "n - 1 < n" "p (n - 1) < n" by auto
    have "coeff_int (\<Prod>i = 0..<n. M $$ (i, p i)) l =
      (\<Prod>i = 0 ..< (n - 1). coeff_int (M $$ (i, p i)) 0) * coeff_int (M $$ (n - 1, p (n - 1))) l"
      unfolding id
    proof (rule coeff_int_prod_const, (auto)[2])
      fix i
      assume "i \<in> {0 ..< n - 1}"
      with p have i: "i \<noteq> n - 1" and "i < n" "p i < n" by (auto simp: n_def)
      note id = subresultant_index_mat[OF this(2-3)[unfolded n_def], folded M_def n_def]
      show "degree (M $$ (i, p i)) = 0" unfolding id Let_def using i
        by (simp split: if_splits)
    qed
    also have "(\<Prod>i = 0 ..< (n - 1). coeff_int (M $$ (i, p i)) 0)
       = (\<Prod>i = 0 ..< (n - 1). L $$ (i, p i))"
    proof (rule prod.cong[OF refl])
      fix i
      assume "i \<in> {0 ..< n - 1}"
      with p have i: "i \<noteq> n - 1" and ii: "i < n" "p i < n" by (auto simp: n_def)
      note id = subresultant_index_mat[OF this(2-3)[unfolded n_def], folded M_def n_def]
      note id' = L_def[unfolded subresultant'_mat_def Let_def, folded n_def] index_mat[OF ii]
      show "coeff_int (M $$ (i, p i)) 0 = L $$ (i, p i)"
        unfolding id id' split using i proof (simp add: if_splits Let_def)
      qed
    qed
    also have "coeff_int (M $$ (n - 1, p (n - 1))) l =
      (if p (n - 1) < degree G - J then
         coeff_int (monom 1 (degree G - J - 1 - p (n - 1)) * F) l
         else coeff_int (monom 1 (degree F - J - 1 - (p (n - 1) - (degree G - J))) * G) l)"
      using subresultant_index_mat[OF n1[unfolded n_def], folded M_def n_def, unfolded idn if_True Let_def]
      by simp
    also have "\<dots> = (if p (n - 1) < degree G - J
      then coeff_int F (int l - int (degree G - J - 1 - p (n - 1)))
      else coeff_int G (int l - int (degree F - J - 1 - (p (n - 1) - (degree G - J)))))"
        unfolding coeff_int_monom_mult by simp
    also have "\<dots> = (if p (n - 1) < degree G - J
      then coeff_int F (int l - int (degree G - J - 1) + p (n - 1))
      else coeff_int G (int l - int (degree F - J - 1) + (p (n - 1) - (degree G - J))))"
    proof (cases "p (n - 1) < degree G - J")
      case True
      hence "int (degree G - J - 1 - p (n - 1)) = int (degree G - J - 1) - p (n - 1)" by simp
      hence id: "int l - int (degree G - J - 1 - p (n - 1)) = int l - int (degree G - J - 1) + p (n - 1)" by simp
      show ?thesis using True unfolding id by simp
    next
      case False
      from n1 False have "degree F - J - 1 \<ge> p (n - 1) - (degree G - J)"
        unfolding n_def by linarith
      hence "int (degree F - J - 1 - (p (n - 1) - (degree G - J))) = int (degree F - J - 1) - (p (n - 1) - (degree G - J))"
        by linarith
      hence id: "int l - int (degree F - J - 1 - (p (n - 1) - (degree G - J))) =
       int l - int (degree F - J - 1) + (p (n - 1) - (degree G - J))" by simp
      show ?thesis unfolding id using False by simp
    qed
    also have "\<dots> = L $$ (n - 1, p (n - 1))"
      unfolding L_def subresultant'_mat_def Let_def n_def[symmetric] using n1 by simp
    also have "(\<Prod>i = 0..<n - 1. L $$ (i, p i)) * \<dots> = (\<Prod>i = 0..<n. L $$ (i, p i))"
      unfolding id by simp
    finally have "coeff_int (\<Prod>i = 0..<n. M $$ (i, p i)) (int l) = (\<Prod>i = 0..<n. L $$ (i, p i))" .
  } note * = this
  have "coeff_int (subresultant J F G) l =
    (\<Sum>p\<in>{p. p permutes {0..<n}}. signof p * coeff_int (\<Prod>i = 0..<n. M $$ (i, p i)) l)"
    unfolding subresultant_def det_def subresultant_mat_dim idn if_True n_def[symmetric] M_def
      coeff_int_sum coeff_int_signof_mult by simp
  also have "\<dots> = (\<Sum>p\<in>{p. p permutes {0..<n}}. signof p * (\<Prod>i = 0..<n. L $$ (i, p i)))"
    by (rule sum.cong[OF refl], insert *, simp)
  also have "\<dots> = det L"
  proof -
    have id: "dim_row (subresultant'_mat J l F G) = n"
      "dim_col (subresultant'_mat J l F G) = n" unfolding subresultant'_mat_def Let_def n_def
      by auto
    show ?thesis unfolding det_def L_def id by simp
  qed
  finally show ?thesis unfolding L_def coeff_int_def using False by auto
qed

lemma subresultant'_zero_ge: assumes "(degree f - J) + (degree g - J) \<noteq> 0" and "k \<ge> degree f + (degree g - J)"
  shows "det (subresultant'_mat J k f g) = 0" (* last row is zero *)
proof -
  obtain dg where dg: "degree g - J = dg" by simp
  obtain df where df: "degree f - J = df" by simp
  obtain ddf where ddf: "degree f = ddf" by simp
  note * = assms(2)[unfolded ddf dg] assms(1)
  define M where "M = (\<lambda> i j. if j < dg
            then coeff_int f (degree f - int i + int j)
            else coeff_int g (degree g - int i + int (j - dg)))"
  let ?M = "subresultant'_mat J k f g"
  have M: "det ?M = det (mat (df + dg) (df + dg)
    (\<lambda>(i, j).
        if i = df + dg - 1 then
          if j < dg
            then coeff_int f (int k - int (dg - 1) + int j)
            else coeff_int g (int k - int (df - 1) + int (j - dg))
        else M i j))" (is "_ = det ?N")
    unfolding subresultant'_mat_def Let_def M_def
    by (rule arg_cong[of _ _ det], rule eq_matI, auto simp: df dg)
  also have "?N = mat (df + dg) (df + dg)
    (\<lambda>(i, j).
        if i = df + dg - 1 then 0
        else M i j)"
    by (rule cong_mat[OF refl refl], unfold split, rule if_cong[OF refl _ refl],
      auto simp add: coeff_int_def df dg ddf intro!: coeff_eq_0, insert *(1),
      unfold ddf[symmetric] dg[symmetric] df[symmetric], linarith+)
  also have "\<dots> = mat\<^sub>r (df + dg) (df + dg) (\<lambda>i. if i = df + dg - 1 then 0\<^sub>v (df + dg) else
    vec (df + dg) (\<lambda> j. M i j))"
    by (rule eq_matI, auto)
  also have "det \<dots> = 0"
    by (rule det_row_0, insert *, auto simp: df[symmetric] dg[symmetric] ddf[symmetric])
  finally show ?thesis .
qed

lemma subresultant'_zero_lt: assumes
  J: "J \<le> degree f" "J \<le> degree g" "J < k"
  and k: "k < degree f + (degree g - J)"
  shows "det (subresultant'_mat J k f g) = 0" (* last row is identical to last row - k *)
proof -
  obtain dg where dg: "dg = degree g - J" by simp
  obtain df where df: "df = degree f - J" by simp
  note * = assms[folded df dg]
  define M where "M = (\<lambda> i j. if j < dg
            then coeff_int f (degree f - int i + int j)
            else coeff_int g (degree g - int i + int (j - dg)))"
  define N where "N = (\<lambda> j. if j < dg
            then coeff_int f (int k - int (dg - 1) + int j)
            else coeff_int g (int k - int (df - 1) + int (j - dg)))"
  let ?M = "subresultant'_mat J k f g"
  have M: "?M = mat (df + dg) (df + dg)
    (\<lambda>(i, j).
        if i = df + dg - 1 then N j
        else M i j)"
    unfolding subresultant'_mat_def Let_def
    by (rule eq_matI, auto simp: df dg M_def N_def)
  also have "\<dots> = mat (df + dg) (df + dg)
    (\<lambda>(i, j).
        if i = df + dg - 1 then N j
        else if i = degree f + dg - 1 - k then N j else M i j)" (is "_ = ?N")
    unfolding N_def
    by (rule cong_mat[OF refl refl], unfold split, rule if_cong[OF refl refl], unfold M_def N_def,
      insert J k, auto simp: df dg intro!: arg_cong[of _ _ "coeff_int _"])
  finally have id: "?M = ?N" .
  have deg: "degree f + dg - 1 - k < df + dg" "df + dg - 1 < df + dg"
    using k J unfolding df dg by auto
  have id: "row ?M (degree f + dg - 1 - k) = row ?M (df + dg - 1)"
    unfolding arg_cong[OF id, of row]
    by (rule eq_vecI, insert deg, auto)
  show ?thesis
    by (rule det_identical_rows[OF _ _ _ _ id, of "df + dg"], insert deg assms,
      auto simp: subresultant'_mat_def Let_def df dg)
qed

lemma subresultant'_mat_sylvester_mat: "transpose_mat (subresultant'_mat 0 0 f g) = sylvester_mat f g"
proof -
  obtain dg where dg: "degree g = dg" by simp
  obtain df where df: "degree f = df" by simp
  let ?M = "transpose_mat (subresultant'_mat 0 0 f g)"
  let ?n = "degree f + degree g"
  have dim: "dim_row ?M = ?n" "dim_col ?M = ?n" by (auto simp: subresultant'_mat_def Let_def)
  show ?thesis
  proof (rule eq_matI, unfold sylvester_mat_dim dim df dg, goal_cases)
    case ij: (1 i j)
    have "?M $$ (i,j) = (if i < dg
         then if j = df + dg - 1
              then coeff_int f (- int (dg - 1) + int i)
              else coeff_int f (int df - int j + int i)
         else if j = df + dg - 1
              then coeff_int g (- int (df - 1) + int (i - dg))
              else coeff_int g (int dg - int j + int (i - dg)))"
      using ij unfolding subresultant'_mat_def Let_def by (simp add: if_splits df dg)
    also have "\<dots> = (if i < dg
         then coeff_int f (int df - int j + int i)
         else coeff_int g (int dg - int j + int (i - dg)))"
    proof -
      have cong: "(b \<Longrightarrow> x = z) \<Longrightarrow> (\<not> b \<Longrightarrow> y = z) \<Longrightarrow> (if b then coeff_int f x else coeff_int f y) = coeff_int f z"
        for b x y z and f :: "'a poly" by auto
      show ?thesis
        by (rule if_cong[OF refl cong cong], insert ij, auto)
    qed
    also have "\<dots> = sylvester_mat f g $$ (i,j)"
    proof -
      have *: "i \<le> j \<Longrightarrow> j - i \<le> df \<Longrightarrow> nat (int df - int j + int i) = df - (j - i)" for j i df
        by simp
      show ?thesis unfolding sylvester_index_mat[OF ij[folded df dg]] df dg
      proof (rule if_cong[OF refl])
        assume i: "i < dg"
        have "int df - int j + int i < 0 \<longrightarrow> \<not> j - i \<le> df" by auto
        thus "coeff_int f (int df - int j + int i) = (if i \<le> j \<and> j - i \<le> df then coeff f (df + i - j) else 0)"
          using i ij by (simp add: coeff_int_def *, intro impI  coeff_eq_0[of f, unfolded df], linarith)
      next
        assume i: "\<not> i < dg"
        hence **: "i - dg \<le> j \<Longrightarrow> dg - (j + dg - i) = i - j" using ij by linarith
        have "int dg - int j + int (i - dg) < 0 \<longrightarrow> \<not> j \<le> i" by auto
        thus "coeff_int g (int dg - int j + int (i - dg)) = (if i - dg \<le> j \<and> j \<le> i then coeff g (i - j) else 0)"
          using ij i by (simp add: coeff_int_def * **, intro impI  coeff_eq_0[of g, unfolded dg], linarith)
      qed
    qed
    finally show ?case .
  qed auto
qed

lemma coeff_subresultant_0_0_resultant: "coeff (subresultant 0 f g) 0 = resultant f g"
proof -
  let ?M = "transpose_mat (subresultant'_mat 0 0 f g)"
  have "det (subresultant'_mat 0 0 f g) = det ?M"
    by (subst det_transpose, auto simp: subresultant'_mat_def Let_def)
  also have "?M = sylvester_mat f g"
    by (rule subresultant'_mat_sylvester_mat)
  finally show ?thesis by (simp add: coeff_subresultant resultant_def)
qed

lemma subresultant_zero_ge: assumes "k \<ge> degree f + (degree g - J)"
  and "(degree f - J) + (degree g - J) \<noteq> 0"
  shows "coeff (subresultant J f g) k = 0"
  unfolding coeff_subresultant
  by (subst subresultant'_zero_ge[OF assms(2,1)], simp)

lemma subresultant_zero_lt: assumes "k < degree f + (degree g - J)"
  and "J \<le> degree f" "J \<le> degree g" "J < k"
  shows "coeff (subresultant J f g) k = 0"
  unfolding coeff_subresultant
  by (subst subresultant'_zero_lt[OF assms(2,3,4,1)], simp)

lemma subresultant_resultant: "subresultant 0 f g = [: resultant f g :]"
proof (cases "degree f + degree g = 0")
  case True
  thus ?thesis unfolding subresultant_def subresultant_mat_def resultant_def Let_def
      sylvester_mat_def sylvester_mat_sub_def
    by simp
next
  case 0: False
  show ?thesis
  proof (rule poly_eqI)
    fix k
    show "coeff (subresultant 0 f g) k = coeff [:resultant f g:] k"
    proof (cases "k = 0")
      case True
      thus ?thesis using coeff_subresultant_0_0_resultant[of f g] by auto
    next
      case False
      hence "0 < k \<and> k < degree f + degree g \<or> k \<ge> degree f + degree g" by auto
      thus ?thesis using subresultant_zero_ge[of f g 0 k] 0
        subresultant_zero_lt[of k f g 0] 0 False by (cases k, auto)
    qed
  qed
qed

lemma (in inj_comm_ring_hom) subresultant_hom:
  "map_poly hom (subresultant J f g) = subresultant J (map_poly hom f) (map_poly hom g)"
proof -
  note d = subresultant_mat_def Let_def
  interpret p: map_poly_inj_comm_ring_hom hom..
  show ?thesis unfolding subresultant_def unfolding p.hom_det[symmetric]
  proof (rule arg_cong[of _ _ det])
    show "p.mat_hom (subresultant_mat J f g) =
      subresultant_mat J (map_poly hom f) (map_poly hom g)"
    proof (rule eq_matI, goal_cases)
      case (1 i j)
      hence ij: "i < degree f - J + (degree g - J)" "j < degree f - J + (degree g - J)"
        unfolding d degree_map_poly by auto
      show ?case
        by (auto simp add: coeff_int_def d map_mat_def index_mat(1)[OF ij] hom_distribs)
    qed (auto simp: d)
  qed
qed

text \<open>We now derive properties of the resultant via the connection to subresultants.\<close>

lemma resultant_smult_left: assumes "(c :: 'a :: idom) \<noteq> 0"
  shows "resultant (smult c f) g = c ^ degree g * resultant f g"
  unfolding coeff_subresultant_0_0_resultant[symmetric] subresultant_smult_left[OF assms] coeff_smult
    by simp

lemma resultant_smult_right: assumes "(c :: 'a :: idom) \<noteq> 0"
  shows "resultant f (smult c g) = c ^ degree f * resultant f g"
  unfolding coeff_subresultant_0_0_resultant[symmetric] subresultant_smult_right[OF assms] coeff_smult
  by simp

lemma resultant_swap: "resultant f g = (-1)^(degree f * degree g) * (resultant g f)"
  unfolding coeff_subresultant_0_0_resultant[symmetric]
  unfolding arg_cong[OF subresultant_swap[of 0 f g], of "\<lambda> x. coeff x 0"] coeff_smult by simp

text \<open>The following equations are taken from Brown-Traub ``On Euclid's Algorithm and
the Theory of Subresultant'' (BT)\<close>

lemma  fixes F B G H :: "'a :: idom poly" and J :: nat
       defines df: "df \<equiv> degree F"
  and dg: "dg \<equiv> degree G"
  and dh: "dh \<equiv> degree H"
  and db: "db \<equiv> degree B"
  defines
    n: "n \<equiv> (df - J) + (dg - J)"
  and f: "f \<equiv> coeff_int F"
  and b: "b \<equiv> coeff_int B"
  and g: "g \<equiv> coeff_int G"
  and h: "h \<equiv> coeff_int H"
  assumes FGH: "F + B * G = H"
  and dfg: "df \<ge> dg"
  and choice: "dg > dh \<or> H = 0 \<and> F \<noteq> 0 \<and> G \<noteq> 0"
shows BT_eq_18: "subresultant J F G = smult ((-1)^((df - J) * (dg - J))) (det (mat n n
  (\<lambda> (i,j).
              if j < df - J
              then if i = n - 1 then monom 1 ((df - J) - 1 - j) * G
                   else [:g (int dg - int i + int j):]
              else if i = n - 1 then monom 1 ((dg - J) - 1 - (j - (df - J))) * H
                   else [:h (int df - int i + int (j - (df - J))):])))"
   (is "_ = smult ?m1 ?right")
  and BT_eq_19: "dh \<le> J \<Longrightarrow> J < dg \<Longrightarrow> subresultant J F G = smult (
    (-1)^((df - J) * (dg - J)) * lead_coeff G ^ (df - J) * coeff H J ^ (dg - J - 1)) H"
    (is "_ \<Longrightarrow> _ \<Longrightarrow> _ = smult (_ * ?G * ?H) H")
  and BT_lemma_1_12: "J < dh \<Longrightarrow> subresultant J F G = smult (
    (-1)^((df - J) * (dg - J)) * lead_coeff G ^ (df - dh)) (subresultant J G H)"
  and BT_lemma_1_13': "J = dh \<Longrightarrow> dg > dh \<or> H \<noteq> 0 \<Longrightarrow> subresultant dh F G = smult (
    (-1)^((df - dh) * (dg - dh)) * lead_coeff G ^ (df - dh) * lead_coeff H ^ (dg - dh - 1)) H"
  and BT_lemma_1_14: "dh < J \<Longrightarrow> J < dg - 1 \<Longrightarrow> subresultant J F G = 0"
  and BT_lemma_1_15': "J = dg - 1 \<Longrightarrow> dg > dh \<or> H \<noteq> 0 \<Longrightarrow> subresultant (dg - 1) F G = smult (
    (-1)^(df - dg + 1) * lead_coeff G ^ (df - dg + 1)) H"
proof -
  define dfj where "dfj = df - J"
  define dgj where "dgj = dg - J"
  note d = df dg dh db
  have F0: "F \<noteq> 0" using dfg choice df by auto
  have G0: "G \<noteq> 0" using choice dg by auto
  have dgh: "dg \<ge> dh" using choice unfolding dh by auto
  have B0: "B \<noteq> 0" using FGH dfg dgh choice F0 G0 unfolding d by auto
  have dfh: "df \<ge> dh" using dfg dgh by auto
  have "df = degree (B * G)"
  proof (cases "H = 0")
    case False
    with choice dfg have dfh: "df > dh" by auto
    show ?thesis using dfh[folded arg_cong[OF FGH, of degree, folded dh]] choice
      unfolding df by (metis \<open>degree (F + B * G) < df\<close> degree_add_eq_left degree_add_eq_right df nat_neq_iff)
  next
    case True
    have "F = - B * G" using arg_cong[OF FGH[unfolded True], of "\<lambda> x. x - B * G"] by auto
    thus ?thesis using F0 G0 B0 unfolding df by simp
  qed
  hence dfbg: "df = db + dg" using degree_mult_eq[OF B0 G0] by (simp add: d)
  hence dbfg: "db = df - dg" by simp
  let ?dfj = "df - J"
  let ?dgj = "dg - J"
  have norm: "?dgj + ?dfj = ?dfj + ?dgj" by simp
  let ?bij = "\<lambda> i j. b (db - int i + int (j - dfj))"
  let ?M = "mat n n (\<lambda> (i,j). if i = j then 1 else if j < dfj then 0 else if i < j
    then [:  ?bij i j :] else 0)" (* this is the matrix which contains all the column-operations
     that are required to transform the subresultant-matrix of F and G into the one of G and H (
     the matrix depicted in equation (18) in BT *)
  let ?GF = "\<lambda> i j.
              if j < dfj
              then if i = n - 1 then monom 1 (dfj - 1 - j) * G
                   else [:g (int dg - int i + int j):]
              else if i = n - 1 then monom 1 (dgj - 1 - (j - dfj)) * F
                   else [:f (int df - int i + int (j - dfj)):]"
  let ?G_F = "mat n n (\<lambda> (i,j). ?GF i j)"
  let ?GH = "\<lambda> i j.
              if j < dfj
              then if i = n - 1 then monom 1 (dfj - 1 - j) * G
                   else [:g (int dg - int i + int j):]
              else if i = n - 1 then monom 1 (dgj - 1 - (j - dfj)) * H
                   else [:h (int df - int i + int (j - dfj)):]"
  let ?G_H = "mat n n (\<lambda> (i,j). ?GH i j)"
  have hfg: "h i = f i + coeff_int (B * G) i" for i
    unfolding FGH[symmetric] f g h unfolding coeff_int_def by simp
  have dM1: "det ?M = 1"
    by (subst det_upper_triangular, (auto)[2], subst prod_list_diag_prod, auto)
  have "subresultant J F G = smult ?m1 (subresultant J G F)"
    unfolding subresultant_swap[of _ F] d by simp
  also have "subresultant J G F = det ?G_F"
    unfolding subresultant_def n norm subresultant_mat_def g f Let_def d[symmetric] dfj_def dgj_def by simp
  also have "\<dots> = det (?G_F * ?M)"
    by (subst det_mult[of _ n], unfold dM1, auto)
  also have "?G_F * ?M = ?G_H"
  proof (rule eq_matI, unfold dim_col_mat dim_row_mat)
    fix i j
    assume i: "i < n" and j: "j < n"
    have "(?G_F * ?M) $$ (i,j) = row (?G_F) i \<bullet> col ?M j"
      using i j by simp
    also have "\<dots> = ?GH i j"
    proof (cases "j < dfj")
      case True
      have id: "col ?M j = unit_vec n j"
        by (rule eq_vecI, insert True i j, auto)
      show ?thesis unfolding id using True i j by simp
    next
      case False
      define d where "d = j - dfj"
      from False have jd: "j = d + dfj" unfolding d_def by auto
      hence idj: "{0 ..< j} = {0 ..< dfj} \<union> {dfj ..< dfj + d}" by auto
      let ?H = "(if i = n - 1 then monom 1 (dgj - Suc d) * H else [:h (int df - int i + int d):])"
      have idr: "?GH i j = ?H" unfolding d_def using jd by auto
      let ?bi = "\<lambda> i. b (db - int i + int d)"
      let ?m = "\<lambda> i. if i = j then 1 else if i < j then [:?bij i j:] else 0"
      let ?P = "\<lambda> k. (?GF i k * ?m k)"
      let ?Q = "\<lambda> k. ?GF i k * [: ?bi k :]"
      let ?G = "\<lambda> k. if i = n - 1 then monom 1 (dfj - 1 - k) * G else [:g (int dg - int i + int k):]"
      let ?Gb = "\<lambda> k. ?G k * [:?bi k:]"
      let ?off = "- (int db - int dfj + 1 + int d)"
      have off0: "?off \<ge> 0" using False dfg j unfolding dfj_def d_def dbfg n by simp
      from nat_0_le[OF this]
      obtain off where off: "int off = ?off" by blast
      have "int off \<le> int dfj" unfolding off by auto
      hence "off \<le> dfj" by simp
      hence split1: "{0 ..< dfj} = {0 ..< off} \<union> {off ..< dfj}" by auto
      have "int off + Suc db \<le> dfj" unfolding off by auto
      hence split2: "{off ..< dfj} = {off .. off + db} \<union> {off + Suc db ..< dfj} " by auto
      let ?g_b = "\<lambda>k. (if i = n - 1 then monom 1 k * G else [:g (int dg - int i + int (dfj - Suc k)):]) *
            [:b (k - int off):]"
      let ?gb = "\<lambda>k. (if i = n - 1 then monom 1 (k + off) * G else [:g (int dg - int i + int (dfj - Suc k - off)):]) *
            [:coeff B k:]"
      let ?F = "\<lambda> k. if i = n - 1 then monom 1 (dgj - 1 - (k - dfj)) * F
                   else [:f (int df - int i + int (k - dfj)):]"
      let ?Fb = "\<lambda> k. ?F k * [:?bi k:]"
      let ?Pj = "if i = n - 1 then  monom 1 (dgj - Suc d) * F else [:f (int df - int i + int d):]"
      from False have id: "col ?M j = vec n ?m"
        using j i by (intro eq_vecI, auto)
      have "row ?G_F i \<bullet> col ?M j = sum ?P {0 ..< n}"
        using i j unfolding id by (simp add: scalar_prod_def)
      also have "{0 ..< n} = {0 ..< j} \<union> {j} \<union> {Suc j ..< n}" using j by auto
      also have "sum ?P \<dots> = sum ?P {0 ..< j} + ?P j + sum ?P {Suc j ..< n}"
        by (simp add: sum.union_disjoint)
      also have "sum ?P {Suc j ..< n} = 0" by (rule sum.neutral, auto)
      also have "?P j = ?Pj"
        unfolding d_def using jd by simp
      also have "sum ?P {0 ..< j} = sum ?Q {0 ..< j}"
        by (rule sum.cong[OF refl], unfold d_def, insert jd, auto)
      also have "sum ?Q {0 ..< j} = sum ?Q {0 ..< dfj} + sum ?Q {dfj ..< dfj+d}" unfolding idj
        by (simp add: sum.union_disjoint)
      also have "sum ?Q {0 ..< dfj} = sum ?Gb {0 ..< dfj}"
        by (rule sum.cong, auto)
      also have "sum ?Q {dfj ..< dfj+d} = sum ?Fb {dfj ..< dfj+d}"
        by (rule sum.cong, auto)
      also have "\<dots> = 0"
      proof (rule sum.neutral, intro ballI)
        fix k
        assume k: "k \<in> {dfj ..< dfj+d}"
        hence k: "db + d < k" using k j False unfolding n db[symmetric] dfbg dfj_def d_def by auto
        let ?k = "(int db - int k + int d)"
        have "?k < 0" using k by auto
        hence "b ?k = 0" unfolding b by (intro coeff_int_eq_0, auto)
        thus "?Fb k = 0" by simp
      qed
      also have "sum ?Gb {0 ..< dfj} = sum ?g_b {0 ..< dfj}"
      proof (rule sum.reindex_cong[of "\<lambda> k. dfj - Suc k"], (auto simp: inj_on_def off)[2], goal_cases)
        case (1 k)
        hence "k = dfj - (Suc (dfj - Suc k))" and "(dfj - Suc k) \<in> {0..<dfj}"  by auto
        thus ?case by blast
      next
        case (2 k)
        hence [simp]: "dfj - Suc (dfj - Suc k) = k"
          "int db - int (dfj - Suc k) + int d = int k - off" by (auto simp: off)
        show ?case by auto
      qed
      also have "\<dots>  = sum ?g_b {0 ..< off} + sum ?g_b {off ..< dfj}" unfolding split1
        by (simp add: sum.union_disjoint)
      also have "sum ?g_b {0 ..< off} = 0"
        by (rule sum.neutral, intro ballI, auto simp: b coeff_int_def)
      also have "sum ?g_b {off ..< dfj} = sum ?g_b {off .. off + db} + sum ?g_b {off + Suc db ..< dfj}"
        unfolding split2 by (rule sum.union_disjoint, auto)
      also have "sum ?g_b {off + Suc db ..< dfj} = 0"
      proof (rule sum.neutral, intro ballI, goal_cases)
        case (1 k)
        hence "b (int k - int off) = 0" unfolding b db
          by (intro coeff_int_eq_0, auto)
        thus ?case by simp
      qed
      also have "sum ?g_b {off .. off + db} = sum ?gb {0 .. db}"
        using sum.atLeastAtMost_shift_bounds [of ?g_b 0 off db]
        by (auto intro: sum.cong simp add: b ac_simps)
      finally have id: "row ?G_F i \<bullet> col ?M j - ?H = ?Pj + sum ?gb {0 .. db} - ?H"
        (is "_ = ?E")
        by (simp add: ac_simps)
      define E where "E = ?E"
      let ?b = "coeff B"
      have Bsum: "(\<Sum>k = 0..db. monom (?b k) k) = B" unfolding db
        using atMost_atLeast0 poly_as_sum_of_monoms by auto
      have "E = 0"
      proof (cases "i = n - 1")
        case i_n: False
        hence id: "(i = n - 1) = False" by simp
        with i have i: "i < n - 1" by auto
        let ?ii = "int df - int i + int d"
        have "?thesis = ([:f ?ii:] +
         (\<Sum>k = 0..db.
          [:g (int dg - int i + int (dfj - Suc k - off)):] * [:?b k:]) -
          [:h ?ii:] = 0)" (is "_ = (?e = 0)") unfolding E_def id if_False by simp
        also have "?e = [: f ?ii +
         (\<Sum>k = 0..db.
          g (int dg - int i + int (dfj - Suc k - off)) * ?b k) -
          h ?ii:]" (is "_ = [: ?e :]")
        proof (rule poly_eqI, goal_cases)
          case (1 n)
          show ?case unfolding coeff_diff coeff_add coeff_sum coeff_const
            by (cases n, auto simp: ac_simps)
        qed
        also have "[: ?e :] = 0 \<longleftrightarrow> ?e = 0" by simp
        also have "?e = (\<Sum>k = 0..db. g (int dg - int i + int (dfj - Suc k - off)) * ?b k)
          - coeff_int (B * G) ?ii"
          unfolding hfg by simp
        also have "(B * G) = (\<Sum>k = 0..db. monom (?b k) k) * G" unfolding Bsum by simp
        also have "\<dots> = (\<Sum>k = 0..db. monom (?b k) k * G)" by (rule sum_distrib_right)
        also have "coeff_int \<dots> ?ii = (\<Sum>k = 0..db. g (?ii - k) * ?b k)"
          unfolding coeff_int_sum coeff_int_monom_mult g by (simp add: ac_simps)
        also have "\<dots> = (\<Sum>k = 0..db. g (int dg - int i + int (dfj - Suc k - off)) * ?b k)"
        proof (rule sum.cong[OF refl], goal_cases)
          case (1 k)
          hence "k \<le> db" by simp
          hence id: "int dg - int i + int (dfj - Suc k - off) = ?ii - k"
            using False i j off dfg
            unfolding dbfg d_def dfj_def n by linarith
          show ?case unfolding id ..
        qed
        finally show ?thesis by simp
      next
        case True
        let ?jj = "dgj - Suc d"
        have zero: "int off - (dgj - Suc d) = 0" using dfg False j unfolding off dbfg dfj_def d_def dgj_def n
          by linarith
        from True have "E = monom 1 ?jj * F + (\<Sum>k = 0.. db.
          monom 1 (k + off) * G * [: ?b k :]) - monom 1 ?jj * H"
          (is "_ = ?A + ?sum - ?mon") unfolding id E_def by simp
        also have "?mon = monom 1 ?jj * F + monom 1 ?jj * (B * G)"
          unfolding FGH[symmetric] by (simp add: ring_distribs)
        also have "?A + ?sum - \<dots> = ?sum - (monom 1 ?jj * G) * B" (is "_ = _ - ?GB * B") by simp
        also have "?sum = (\<Sum>k = 0..db.
          (monom 1 ?jj * G) * (monom 1 (k + off - ?jj) * [: ?b k :]))"
        proof (rule sum.cong[OF refl], goal_cases)
          case (1 k)
          let ?one = "1 :: 'a"
          have "int off \<ge> int ?jj" using j False i True
            unfolding off d_def dfj_def dgj_def dfbg n by linarith
          hence "k + off = ?jj + (k + off - ?jj)" by linarith
          hence id: "monom ?one (k + off) = monom (1 * 1) (?jj + (k + off - ?jj))" by simp
          show ?case unfolding id[folded mult_monom] by (simp add: ac_simps)
        qed
        also have "\<dots> = (monom 1 ?jj * G) * (\<Sum>k = 0..db.  monom 1 (k + off - ?jj) * [:?b k:])"
          (is "_ = _ * ?sum")
          unfolding sum_distrib_left ..
        also have "\<dots> - (monom 1 ?jj * G) * B = (monom 1 ?jj * G) * (?sum - B)" by (simp add: ring_distribs)
        also have "?sum = (\<Sum>k = 0..db.  monom 1 k * [:?b k:])"
          by (rule sum.cong[OF refl], insert zero, auto)
        also have "\<dots> = (\<Sum>k = 0..db.  monom (?b k) k)"
          by (rule sum.cong[OF refl], rule poly_eqI, auto)
        also have "\<dots> = B" unfolding Bsum ..
        finally show ?thesis by simp
      qed
      from id[folded E_def, unfolded this]
      show ?thesis using False unfolding d_def by simp
    qed
    also have "\<dots> = ?G_H $$ (i,j)" using i j by simp
    finally show "(?G_F * ?M) $$ (i,j) = ?G_H $$ (i,j)" .
  qed auto
  finally show eq_18: "subresultant J F G = smult ?m1 (det ?G_H)" unfolding dfj_def dgj_def .
  {
    fix i j
    assume ij: "i < j" and j: "j < n"
    with dgh have "int dg - int i + int j > int dg" by auto
    hence "g (int dg - int i + int j) = 0" unfolding g dg by (intro coeff_int_eq_0, auto)
  } note g0 = this
  {
    assume *: "dh \<le> J" "J < dg"
    have n_dfj: "n > dfj" using * unfolding n dfj_def by auto
    note eq_18
    also have "det ?G_H = prod_list (diag_mat ?G_H)"
    proof (rule det_lower_triangular[of n])
      fix i j
      assume ij: "i < j" and j: "j < n"
      from ij j have if_e: "i = n - 1 \<longleftrightarrow> False" by auto
      have "?G_H $$ (i,j) = ?GH i j" using ij j by auto
      also have "\<dots> = 0"
      proof (cases "j < dfj")
        case True
        with True g0[OF ij j] show ?thesis unfolding if_e by simp
      next
        case False
        have "h (int df - int i + int (j - dfj)) = 0" unfolding h
          by (rule coeff_int_eq_0, insert False * ij j dfg, unfold dfj_def dh[symmetric], auto)
        with False show ?thesis unfolding if_e by auto
      qed
      finally show "?G_H $$ (i,j) = 0" .
    qed auto
    also have "\<dots> = (\<Prod>i = 0..<n. ?GH i i)"
      by (subst prod_list_diag_prod, simp)
    also have "{0 ..< n} = {0 ..< dfj} \<union> {dfj ..< n}" unfolding n dfj_def by auto
    also have "prod (\<lambda> i. ?GH i i) \<dots> = prod (\<lambda> i. ?GH i i) {0 ..< dfj} * prod (\<lambda> i. ?GH i i) {dfj ..< n}"
      by (simp add: prod.union_disjoint)
    also have "prod (\<lambda> i. ?GH i i) {0 ..< dfj} = prod (\<lambda> i. [: lead_coeff G :]) {0 ..< dfj}"
    proof -
      show ?thesis
        by (rule prod.cong[OF refl], insert n_dfj, auto simp: g coeff_int_def dg)
    qed
    also have "\<dots> = [: (lead_coeff G)^dfj :]" by (simp add: poly_const_pow)
    also have "{dfj ..< n} = {dfj ..< n-1} \<union> {n - 1}" using n_dfj by auto
    also have "prod (\<lambda> i. ?GH i i) \<dots> = prod (\<lambda> i. ?GH i i) {dfj ..< n-1} * ?GH (n - 1) (n - 1)"
      by (simp add: prod.union_disjoint)
    also have "?GH (n - 1) (n - 1) = H"
    proof -
      have "dgj - 1 - (n - 1 - dfj) = 0" using n_dfj unfolding dgj_def dfj_def n by auto
      with n_dfj show ?thesis by auto
    qed
    also have "prod (\<lambda> i. ?GH i i) {dfj ..< n-1} = prod (\<lambda> i. [:h (int df - dfj):]) {dfj ..< n-1}"
      by (rule prod.cong[OF refl], auto intro!: arg_cong[of _ _ h])
    also have "\<dots> = [: h (int df - dfj) ^ (n - 1 - dfj) :]"
      unfolding prod_constant by (simp add: poly_const_pow)
    also have "n - 1 - dfj = dg - J - 1" unfolding n dfj_def by simp
    also have "int df - dfj = J" using * dfg unfolding dfj_def by auto
    also have "h J = coeff H J" unfolding h coeff_int_def by simp
    finally show "subresultant J F G = smult (?m1 * ?G * ?H) H" by (simp add: dfj_def ac_simps)
  } note eq_19 = this
  {
    assume J: "J < dh"
    define dhj where "dhj = dh - J"
    have n_add: "n = (df - dh) + (dhj + dgj)" unfolding dhj_def dgj_def n using J dfg dgh by auto
    let ?split = "split_block ?G_H (df - dh) (df - dh)"
    have dim: "dim_row ?G_H = (df - dh) + (dhj + dgj)"
      "dim_col ?G_H = (df - dh) + (dhj + dgj)"
      unfolding n_add by auto
    obtain UL UR LL LR where spl: "?split = (UL,UR,LL,LR)" by (cases ?split, auto)
    note spl' = spl[unfolded split_block_def Let_def, simplified]
    let ?LR = "subresultant_mat J G H"
    have "LR = mat (dgj + dhj) (dgj + dhj)
       (\<lambda> (i,j). ?GH (i + (df - dh)) (j + (df - dh)))"
      using spl' by (auto simp: n_add)
    also have "\<dots> = ?LR"
      unfolding subresultant_mat_def Let_def dhj_def dgj_def d[symmetric]
    proof (rule eq_matI, unfold dim_row_mat dim_col_mat index_mat split dfj_def, goal_cases)
      case (1 i j)
      hence id1: "(j + (df - dh) < df - J) = (j < dh - J)" using dgh dfg J by auto
      have id2: "(i + (df - dh) = n - 1) = (i = dg - J + (dh - J) - 1)"
        unfolding n_add dhj_def dgj_def using dgh dfg J by auto
      have id3: "(df - J - 1 - (j + (df - dh))) = (dh - J - 1 - j)"
        and id4: "(int dg - int (i + (df - dh)) + int (j + (df - dh))) = (int dg - int i + int j)"
        and id5: "(dg - J - 1 - (j + (df - dh) - (df - J))) = (dg - J - 1 - (j - (dh - J)))"
        and id6: "(int df - int (i + (df - dh)) + int (j + (df - dh) - (df - J))) = (int dh - int i + int (j - (dh - J)))"
        using dgh dfg J by auto
      show ?case unfolding g[symmetric] h[symmetric] id3 id4 id5 id6
        by (rule if_cong[OF id1 if_cong[OF id2 refl refl] if_cong[OF id2 refl refl]])
    qed auto
    finally have "LR = ?LR" .
    note spl = spl[unfolded this]
    let ?UR = "0\<^sub>m (df - dh) (dgj + dhj)"
    have "UR = mat (df - dh) (dgj + dhj)
       (\<lambda> (i,j). ?GH i (j + (df - dh)))"
      using spl' by (auto simp: n_add)
    also have "\<dots> = ?UR"
    proof (rule eq_matI, unfold dim_row_mat dim_col_mat index_mat split dfj_def index_zero_mat, goal_cases)
      case (1 i j)
      hence in1: "i \<noteq> n - 1" using J unfolding dgj_def dhj_def n_add by auto
      {
        assume "j + (df - dh) < df - J"
        hence "dg < int dg - int i + int (j + (df - dh))" using 1 J unfolding dgj_def dhj_def by auto
        hence "g \<dots> = 0" unfolding dg g by (intro coeff_int_eq_0, auto)
      } note g = this
      {
        assume "\<not> (j + (df - dh) < df - J)"
        hence "dh < int df - int i + int (j + (df - dh) - (df - J))" using 1 J unfolding dgj_def dhj_def by auto
        hence "h \<dots> = 0" unfolding dh h by (intro coeff_int_eq_0, auto)
      } note h = this
      show ?case using in1 g h by auto
    qed auto
    finally have "UR = ?UR" .
    note spl = spl[unfolded this]
    let ?G = "\<lambda> (i,j). if i = j then [:lead_coeff G:] else if i < j then 0 else ?GH i j"
    let ?UL = "mat (df - dh) (df - dh) ?G"
    have "UL = mat (df - dh) (df - dh) (\<lambda> (i,j). ?GH i j)"
      using spl' by (auto simp: n_add)
    also have "\<dots> = ?UL"
    proof (rule eq_matI, unfold dim_row_mat dim_col_mat index_mat split, goal_cases)
      case (1 i j)
      {
        assume "i = j"
        hence "int dg - int i + int j = dg" using 1 by auto
        hence "g (int dg - int i + int j) = lead_coeff G"
          unfolding g dg coeff_int_def by simp
      } note eq = this
      {
        assume "i < j"
        hence "dg < int dg - int i + int j" using 1 by auto
        hence "g (int dg - int i + int j) = 0"
          unfolding g dg by (intro coeff_int_eq_0, auto)
      } note lt = this
      from 1 have *: "j < dfj" "i \<noteq> n - 1" using J unfolding n_add dhj_def dgj_def dfj_def  by auto
      hence "?GH i j = [:g (int dg - int i + int j):]" by simp
      also have "\<dots> = (if i = j then [: lead_coeff G :] else if i < j then 0 else ?GH i j)"
        using eq lt * by auto
      finally show ?case by simp
    qed auto
    finally have "UL = ?UL" .
    note spl = spl[unfolded this]
    from split_block[OF spl dim]
    have GH: "?G_H = four_block_mat ?UL ?UR LL ?LR"
      and C: "?UL \<in> carrier_mat (df - dh) (df - dh)"
      "?UR \<in> carrier_mat (df - dh) (dhj + dgj)"
      "LL \<in> carrier_mat (dhj + dgj) (df - dh)"
      "?LR \<in> carrier_mat (dhj + dgj) (dhj + dgj)" by auto
    from arg_cong[OF GH, of det]
    have "det ?G_H = det (four_block_mat ?UL ?UR LL ?LR)" unfolding GH[symmetric] ..
    also have "\<dots> = det ?UL * det ?LR"
      by (rule det_four_block_mat_upper_right_zero[OF _ refl], insert C, auto simp: ac_simps)
    also have "det ?LR = subresultant J G H" unfolding subresultant_def by simp
    also have "det ?UL = prod_list (diag_mat ?UL)"
      by (rule det_lower_triangular[of "df - dh"], auto)
    also have "\<dots> = (\<Prod>i = 0..< (df - dh). [: lead_coeff G :])" unfolding prod_list_diag_prod by simp
    also have "\<dots> = [: lead_coeff G ^ (df - dh) :]" by (simp add: poly_const_pow)
    finally have det: "det ?G_H = [:lead_coeff G ^ (df - dh):] * subresultant J G H" by auto
    show "subresultant J F G = smult (?m1 * lead_coeff G ^ (df - dh)) (subresultant J G H)"
      unfolding eq_18 det by simp
  }
  {
    assume J: "dh < J" "J < dg - 1"
    hence "dh \<le> J" "J < dg" by auto
    from eq_19[OF this]
    have "subresultant J F G = smult ((- 1) ^ ((df - J) * (dg - J)) * lead_coeff G ^ (df - J) * coeff H J ^ (dg - J - 1)) H"
      by simp
    also have "coeff H J = 0" by (rule coeff_eq_0, insert J, auto simp: dh)
    also have "\<dots> ^ (dg - J - 1) = 0" using J by auto
    finally show "subresultant J F G = 0" by simp
  }
  {
    assume J: "J = dh" and "dg > dh \<or> H \<noteq> 0"
    with choice have dgh: "dg > dh" by auto
    show "subresultant dh F G = smult (
      (-1)^((df - dh) * (dg - dh)) * lead_coeff G ^ (df - dh) * lead_coeff H ^ (dg - dh - 1)) H"
      unfolding eq_19[unfolded J, OF le_refl dgh] unfolding dh by simp
  }
  {
    assume J: "J = dg - 1" and "dg > dh \<or> H \<noteq> 0"
    with choice have dgh: "dg > dh" by auto
    have *: "dh \<le> dg - 1" "dg - 1 < dg" using dgh by auto
    have **: "df - (dg - 1) = df - dg + 1" "dg - (dg - 1) - 1 = 0" "dg - (dg - 1) = 1"
      using dfg dgh by linarith+
    show "subresultant (dg - 1) F G = smult (
      (-1)^(df - dg + 1) * lead_coeff G ^ (df - dg + 1)) H"
      unfolding eq_19[unfolded J, OF *] unfolding ** by simp
  }
qed

lemmas BT_lemma_1_13 = BT_lemma_1_13'[OF _ _ _ refl]
lemmas BT_lemma_1_15 = BT_lemma_1_15'[OF _ _ _ refl]

lemma subresultant_product: fixes F :: "'a :: idom poly"
  assumes "F = B * G"
  and FG: "degree F \<ge> degree G"
shows "subresultant J F G = (if J < degree G then 0 else
   if J < degree F then smult (lead_coeff G ^ (degree F - J - 1)) G else 1)"
proof (cases "J < degree G")
  case J: True
  from assms have eq: "F + (-B) * G = 0" by auto
  from J have lt: "degree 0 < degree G \<or> b" for b by auto
  from BT_lemma_1_13[OF eq FG lt lt]
  have "subresultant 0 F G = 0" using J by auto
  with BT_lemma_1_14[OF eq FG lt, of J] have 00: "J = 0 \<or> J < degree G - 1 \<Longrightarrow> subresultant J F G = 0" by auto
  from BT_lemma_1_15[OF eq FG lt lt] J have 01: "subresultant (degree G - 1) F G = 0" by simp
  from J have "(J = 0 \<or> J < degree G - 1) \<or> J = degree G - 1" by linarith
  with 00 01 have "subresultant J F G = 0" by auto
  thus ?thesis using J by simp
next
  case J: False
  hence dg: "degree G - J = 0" by simp
  let ?n = "degree F - J"
  have *: "(j :: nat) < 0 \<longleftrightarrow> False" "j - 0 = j" for j by auto
  let ?M = "mat ?n ?n
          (\<lambda>(i, j).
              if i = ?n - 1 then monom 1 (?n - 1 - j) * G
              else [:coeff_int G (int (degree G) - int i + int j):])"
  have "subresultant J F G = det ?M"
    unfolding subresultant_def subresultant_mat_def Let_def dg * by auto
  also have "det ?M = prod_list (diag_mat ?M)"
    by (rule det_lower_triangular[of ?n], auto intro: coeff_int_eq_0)
  also have "\<dots> = (\<Prod>i = 0..< ?n. ?M $$ (i,i))" unfolding prod_list_diag_prod by simp
  also have "\<dots> = (\<Prod>i = 0..< ?n. if i = ?n - 1 then G else [: lead_coeff G :])"
    by (rule prod.cong[OF refl], auto simp: coeff_int_def)
  also have "\<dots> = (if J < degree F then smult (lead_coeff G ^ (?n - 1)) G else 1)"
  proof (cases "J < degree F")
    case True
    hence id: "{ 0 ..< ?n} = { 0 ..< ?n - 1} \<union> {?n - 1}" by auto
    have "(\<Prod>i = 0..< ?n. if i = ?n - 1 then G else [: lead_coeff G :])
      = (\<Prod>i = 0 ..< ?n - 1. if i = ?n - 1 then G else [: lead_coeff G :]) * G" (is "_ = ?P * G")
      unfolding id
      by (subst prod.union_disjoint, auto)
    also have "?P = (\<Prod>i = 0 ..< ?n - 1. [: lead_coeff G :])"
      by (rule prod.cong, auto)
    also have "\<dots> = [: lead_coeff G ^ (?n - 1) :]"
      by (simp add: poly_const_pow)
    finally show ?thesis by auto
  qed auto
  finally have "subresultant J F G =
      (if J < degree F then smult (lead_coeff G ^ (degree F - J - 1)) G else 1)" .
  thus ?thesis using J by simp
qed

lemma resultant_pseudo_mod_0: assumes "pseudo_mod f g = (0 :: 'a :: idom_divide poly)"
  and dfg: "degree f \<ge> degree g"
  and f: "f \<noteq> 0" and g: "g \<noteq> 0"
  shows "resultant f g = (if degree g = 0 then lead_coeff g^degree f else 0)"
proof -
  let ?df = "degree f" let ?dg = "degree g"
  obtain d r where pd: "pseudo_divmod f g = (d,r)" by force
  from pd have r: "r = pseudo_mod f g" unfolding pseudo_mod_def by simp
  with assms pd have pd: "pseudo_divmod f g = (d,0)" by auto
  from pseudo_divmod[OF g pd] g
  obtain a q where prod: "smult a f = g * q" and a: "a \<noteq> 0" "a = lead_coeff g ^ (Suc ?df - ?dg)"
    by auto
  from a dfg have dfg: "degree g \<le> degree (smult a f)" by auto
  have g0: "degree g = 0 \<Longrightarrow> coeff g 0 = 0 \<Longrightarrow> g = 0"
    using leading_coeff_0_iff by fastforce
  from prod have "smult a f = q * g" by simp
  from arg_cong[OF subresultant_product[OF this dfg, of 0, unfolded subresultant_resultant
    resultant_smult_left[OF a(1)]], of "\<lambda> x. coeff x 0"]
  show ?thesis using a g0 by (cases "degree f", auto)
qed

locale primitive_remainder_sequence =
  fixes F :: "nat \<Rightarrow> 'a :: idom_divide poly"
    and n :: "nat \<Rightarrow> nat"
    and \<delta> :: "nat \<Rightarrow> nat"
    and f :: "nat \<Rightarrow> 'a"
    and k :: nat
    and \<beta> :: "nat \<Rightarrow> 'a"
  assumes f: "\<And> i. f i = lead_coeff (F i)"
      and n: "\<And> i. n i = degree (F i)"
      and \<delta>: "\<And> i. \<delta> i = n i - n (Suc i)"
      and n12: "n 1 \<ge> n 2"
      and F12: "F 1 \<noteq> 0" "F 2 \<noteq> 0"
      and F0: "\<And> i. i \<noteq> 0 \<Longrightarrow> F i = 0 \<longleftrightarrow> i > k"
      and \<beta>0: "\<And> i. \<beta> i \<noteq> 0"
      and pmod: "\<And> i. i \<ge> 3 \<Longrightarrow> i \<le> Suc k \<Longrightarrow> smult (\<beta> i) (F i) = pseudo_mod (F (i - 2)) (F (i - 1))"
begin

lemma f10: "f 1 \<noteq> 0" and f20: "f 2 \<noteq> 0" unfolding f using F12 by auto

lemma f0: "i \<noteq> 0 \<Longrightarrow> f i = 0 \<longleftrightarrow> i > k"
  using F0[of i] unfolding f by auto

lemma n_gt: assumes "2 \<le> i" "i < k"
  shows "n i > n (Suc i)"
proof -
  from assms have "3 \<le> Suc i" "Suc i \<le> Suc k" by auto
  note pmod = pmod[OF this]
  from assms F0 have "F (Suc i - 1) \<noteq> 0" "F (Suc i) \<noteq> 0" by auto
  from pseudo_mod(2)[OF this(1), of "F (Suc i - 2)", folded pmod] this(2)
  show ?thesis unfolding n using \<beta>0 by auto
qed


lemma n_ge: assumes "1 \<le> i" "i < k"
  shows "n i \<ge> n (Suc i)"
  using n12 n_gt[OF _ assms(2)] assms(1) by (cases "i = 1", auto simp: numeral_2_eq_2)

lemma n_ge_trans: assumes "1 \<le> i" "i \<le> j" "j \<le> k"
  shows "n i \<ge> n j"
proof -
  from assms(2) have "j = i + (j - i)" by simp
  then obtain jj where j: "j = i + jj" by blast
  from assms(3)[unfolded j] show ?thesis unfolding j
  proof (induct jj)
    case (Suc j)
    from Suc(2) have "i + j \<le> k" by simp
    from Suc(1)[OF this] have IH: "n (i + j) \<le> n i" .
    have "n (Suc (i + j)) \<le> n (i + j)"
      by (rule n_ge, insert assms(1) Suc(2), auto)
    with IH show ?case by auto
  qed auto
qed

lemma delta_gt: assumes "2 \<le> i" "i < k"
  shows "\<delta> i > 0" using n_gt[OF assms] unfolding \<delta> by auto

lemma k2:"2 \<le> k"
  by (metis le_cases linorder_not_le F0 F12(2) zero_order(2))

lemma k0: "k \<noteq> 0" using k2 by auto


lemma ni2:"3 \<le> i \<Longrightarrow> i \<le> k \<Longrightarrow> n i \<noteq> n 2"
  by (metis Suc_numeral \<delta> delta_gt k2 le_imp_less_Suc le_less n_ge_trans not_le one_le_numeral
      semiring_norm(5) zero_less_diff)
end


locale subresultant_prs_locale = primitive_remainder_sequence F n \<delta> f k \<beta> for
       F :: "nat \<Rightarrow> 'a :: idom_divide fract poly"
    and n :: "nat \<Rightarrow> nat"
    and \<delta> :: "nat \<Rightarrow> nat"
    and f :: "nat \<Rightarrow> 'a fract"
    and k :: nat
    and \<beta> :: "nat \<Rightarrow> 'a fract" +
  fixes G1 G2 :: "'a poly"
  assumes F1: "F 1 = map_poly to_fract G1"
    and F2: "F 2 = map_poly to_fract G2"
begin

definition "\<alpha> i = (f (i - 1))^(Suc (\<delta> (i - 2)))"

lemma \<alpha>0: "i > 1 \<Longrightarrow> \<alpha> i = 0 \<longleftrightarrow> (i - 1) > k"
  unfolding \<alpha>_def using f0[of "i - 1"] by auto

lemma \<alpha>_char:
assumes "3 \<le> i" "i < k + 2"
  shows "\<alpha> i = (f (i - 1)) ^ (Suc (length (coeffs (F (i - 2)))) - length (coeffs (F (i - 1))))"
proof (cases "i = 3")
  case True
  have triv:"Suc (Suc 0) = 2" by auto
  have l:"length (coeffs (F 2)) \<noteq> 0" "length (coeffs (F 1)) \<noteq> 0" using F12 by auto
  hence "length (coeffs (F 2)) \<le> length (coeffs (F (Suc 0)))" using n12
    unfolding n degree_eq_length_coeffs One_nat_def by linarith
  hence "Suc (length (coeffs (F 1)) - 1 - (length (coeffs (F 2)) - 1)) =
         (Suc (length (coeffs (F 1))) - length (coeffs (F (3 - 1))))" using l by simp
  thus ?thesis unfolding True \<alpha>_def n \<delta> degree_eq_length_coeffs by (simp add:triv)
next
  case False
  hence assms:"2 \<le> i - 2" "i - 2 < k" using assms by auto
  have i:"i - 2 \<noteq> 0" "i - 1 \<noteq> 0" using assms by auto
  hence [simp]: "Suc (i - 2) = i - 1" by auto
  from assms(2) F0[OF i(2)] have "F (i - 1) \<noteq> 0" by auto
  then have "length (coeffs (F (i - 1))) > 0" by (cases "F (i - 1)") auto
  with delta_gt[unfolded \<delta> n degree_eq_length_coeffs,OF assms]
  have * : "Suc (\<delta> (i - 2)) = Suc (length (coeffs (F (i - 2)))) - (length (coeffs (F (Suc (i - 2)))))"
    by (auto simp:\<delta> n degree_eq_length_coeffs)
  show ?thesis unfolding \<alpha>_def * by simp
qed

definition Q :: "nat \<Rightarrow> 'a fract poly" where
  "Q i \<equiv> smult (\<alpha> i) (fst (pdivmod (F (i - 2)) (F (i - 1))))"

lemma beta_F_as_sum:
  assumes "3 \<le> i" "i \<le> Suc k"
  shows "smult (\<beta> i) (F i) = smult (\<alpha> i) (F (i - 2)) + - Q i * F (i - 1)" (is ?t1)
proof -
  have ik:"i < k + 2" using assms by auto
  have f0:"F (i - 1) = 0 \<longleftrightarrow> False" "F (i - Suc 0) = 0 \<longleftrightarrow> False"
    using F0[of "i - 1"] assms by auto
  hence f0_b:"(inverse (coeff (F (i - 1)) (degree (F (i - 1))))) \<noteq> 0" "F (i - 1) \<noteq> 0" by auto
  have i:"i - 2 \<noteq> 0" "Suc (i - 2) = i - 1" "(k < i - 2) \<longleftrightarrow> False" using assms by auto
  have "F (i - 2) \<noteq> 0" using F0[of "i - 2"] assms by auto
  let ?c = "(inverse (f (i - 1)) ^ (Suc (length (coeffs (F (i - 2)))) - length (coeffs (F (i - 1)))))"
  have inv:"inverse (\<alpha> i) = ?c" unfolding \<alpha>_char[OF assms(1) ik] power_inverse by auto
  have alpha0:"\<alpha> i \<noteq> 0" unfolding \<alpha>_def f using f0 by auto
  have \<alpha>_inv[simp]:"\<alpha> i * inverse (\<alpha> i) = 1"
    using field_class.field_inverse[OF alpha0] mult.commute by metis
  with field_class.field_inverse[OF alpha0,unfolded inv]
  have c_times_Q:"smult ?c (Q i) = fst (pdivmod (F (i - 2)) (F (i - 1)))"
    unfolding Q_def by auto
  have "pdivmod (F (i - 2)) (F (i - 1)) = (smult ?c (Q i), smult ?c (smult (\<beta> i) (F i)))"
    unfolding c_times_Q
    unfolding pdivmod_via_pseudo_divmod pmod[OF assms] f n c_times_Q
              pseudo_mod_smult_right[OF f0_b, of "F (i - 2)",symmetric] f0 if_False Let_def
    unfolding pseudo_mod_def by (auto split:prod.split)
  from this[folded pdivmod_pdivmodrel]
  have pr:"F (i - 2) = smult ?c (Q i) * F (i - 1) + smult ?c ( smult (\<beta> i) (F i))"
    by (auto simp: eucl_rel_poly_iff)
  hence "F (i - 2) = smult (inverse (\<alpha> i)) (Q i) * F (i - 1)
                   + smult (inverse (\<alpha> i)) ( smult (\<beta> i) (F i))" (is "?l = ?r" is "_ = ?t + _")
                   unfolding inv.
  hence eq:"smult (\<alpha> i) (?l - ?t) = smult (\<alpha> i) (?r - ?t)" by auto
  have " smult (\<alpha> i) (F (i - 2)) - Q i * (F (i - 1)) = smult (\<alpha> i) (?l - ?t)"
   unfolding smult_diff_right by auto
  also have "\<dots> = smult (\<alpha> i) (?r - ?t)" unfolding eq..
  also have "\<dots> = smult (\<beta> i) (F i)" by (auto simp:mult.assoc[symmetric])
  finally show ?t1 by auto
qed

lemma assumes "3 \<le> i" "i \<le> k" shows
  BT_lemma_2_21: "j < n i \<Longrightarrow> smult (\<alpha> i ^ (n (i - 1) - j)) (subresultant j (F (i - 2)) (F (i - 1)))
  = smult ((- 1) ^ ((n (i - 2) - j) * (n (i - 1) - j)) * (f (i - 1)) ^ (\<delta> (i - 2) + \<delta> (i - 1)) * (\<beta> i) ^ (n (i - 1) - j)) (subresultant j (F (i - 1)) (F i))"
    (is "_ \<Longrightarrow> ?eq_21") and
  BT_lemma_2_22: "smult (\<alpha> i ^ (\<delta> (i - 1))) (subresultant (n i) (F (i - 2)) (F (i - 1)))
  = smult ((- 1) ^ ((\<delta> (i - 2) + \<delta> (i - 1)) * \<delta> (i - 1)) * f (i - 1) ^ (\<delta> (i - 2) + \<delta> (i - 1)) * f i ^ (\<delta> (i - 1) - 1) * (\<beta> i) ^ \<delta> (i - 1)) (F i)"
    (is "?eq_22") and
  BT_lemma_2_23: "n i < j \<Longrightarrow> j < n (i - 1) - 1 \<Longrightarrow> subresultant j (F (i - 2)) (F (i - 1)) = 0"
    (is "_ \<Longrightarrow> _ \<Longrightarrow> ?eq_23") and
  BT_lemma_2_24: "smult (\<alpha> i) (subresultant (n (i - 1) - 1) (F (i - 2)) (F (i - 1)))
  = smult ((- 1) ^ (\<delta> (i - 2) + 1) * f (i - 1) ^ (\<delta> (i - 2) + 1) * \<beta> i) (F i)" (is "?eq_24")
proof -
  from assms have ik:"i \<le> Suc k" by auto
  note beta_F_as_sum = beta_F_as_sum[OF assms(1) ik, symmetric]
  have s[simp]:"Suc (i - 2) = i - 1" "Suc (i - 1) = i" using assms by auto
  have \<alpha>0:"\<alpha> i \<noteq> 0" using assms f0[of "i - 1"] unfolding \<alpha>_def f by auto
  hence \<alpha>0pow:"\<And> x. \<alpha> i ^ x \<noteq> 0" by auto
  have df:"degree (F (i - 1)) \<le> degree (smult (\<alpha> i) (F (i - 2)))"
          "degree (smult (\<beta> i) (F i)) < degree (F (i - 1)) \<or> b" for b
    using n_ge[of "i-2"] n_gt[of "i-1"] assms \<alpha>0 \<beta>0 unfolding n by auto
  have degree_smult_eq:"\<And> c f. (c::_::{idom_divide}) \<noteq> 0 \<Longrightarrow> degree (smult c f) = degree f" by auto
  have n_lt:"n i < n (i - 1)" using n_gt[of "i-1"] assms unfolding n by auto
  from semiring_normalization_rules(30) mult.commute
    have *:"\<And> x y q. (x * (y::'a fract)) ^ q = y ^ q * x ^ q" by metis
  have "n (i - 1) - n i > 0" using n_lt by auto
  hence **:"\<beta> i ^ (n (i - 1) - n i - 1) * \<beta> i = \<beta> i ^ (n (i - 1) - n i)"
    by (subst power_minus_mult) auto
  have "max (n (i - 2)) (n (i - 1)) = n (i - 2)" using n_ge[of "i-2"] assms
    unfolding max_def by auto
  with diff_add_assoc[OF n_ge[of "i-1"],symmetric] assms
  have ns : "n (i - 2) - n (i - 1) + (n (i - 1) - n i) = n (i - 2) - n i"
     by (auto simp:nat_minus_add_max)
  { assume "j < n i"
    hence j:"j < degree (smult (\<beta> i) (F i))" using \<beta>0 unfolding n by auto
    from BT_lemma_1_12[OF beta_F_as_sum df j]
    show ?eq_21
      unfolding subresultant_smult_right[OF \<beta>0] subresultant_smult_left[OF \<alpha>0]
                degree_smult_eq[OF \<alpha>0] degree_smult_eq[OF \<beta>0] n[symmetric] f[symmetric] \<delta> s ns
      using f n
      by auto}
  { from BT_lemma_1_13[OF beta_F_as_sum df df(2)]
    show ?eq_22
      unfolding subresultant_smult_left[OF \<alpha>0] lead_coeff_smult smult_smult
                degree_smult_eq[OF \<alpha>0] degree_smult_eq[OF \<beta>0] n[symmetric] f[symmetric] \<delta> s ns
      by (metis (no_types, lifting) * ** coeff_smult f mult.assoc n)}
  { assume "n i < j" "j < n (i - 1) - 1"
    hence j:"degree (smult (\<beta> i) (F i)) < j" "j < degree (F (i - 1)) - 1"
      using \<beta>0 unfolding n by auto
    from BT_lemma_1_14[OF beta_F_as_sum df j]
    show ?eq_23 unfolding subresultant_smult_left[OF \<alpha>0] smult_eq_0_iff using \<alpha>0pow by auto}
  { have ***: "n (i - 1) - (n (i - 1) - 1) = 1" using n_lt by auto
    from BT_lemma_1_15[OF beta_F_as_sum df df(2)]
    show ?eq_24
      unfolding subresultant_smult_left[OF \<alpha>0] *** degree_smult_eq[OF \<alpha>0] n[symmetric] f \<delta>
      by (auto simp:mult.commute)}
qed

lemma BT_eq_30: "3 \<le> i \<Longrightarrow> i \<le> k + 1 \<Longrightarrow> j < n (i - 1) \<Longrightarrow>
    smult (\<Prod>l\<leftarrow>[3..<i]. \<alpha> l ^ (n (l - 1) - j)) (subresultant j (F 1) (F 2))
  = smult (\<Prod>l\<leftarrow>[3..<i]. \<beta> l ^ (n (l - 1) - j) * f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1))
        * (- 1) ^ ((n (l - 2) - j) * (n (l - 1) - j))) (subresultant j (F (i - 2)) (F (i - 1)))"
proof (induct "i - 3" arbitrary:i)
  case (Suc x)
  from Suc.hyps(2) Suc.prems(1-2)
    have prems:"x = (i - 1) - 3" "3 \<le> i - 1" "i - 1 \<le> k + 1" "2 \<le> i - 1 - 1" "i - 1 - 1 < k"
               "i - 1 \<le> k" by auto
  from prems(2) have inset:"i - 1 \<in> set [3..<i]" by auto
  have r1:"remove1 (i - 1) [3..<i] = [3..<i-1]" by (induct i,auto simp:remove1_append)
  from Suc.prems(1) have "Suc (i - 1 - 1) = i - 1" by auto
  from n_gt[OF prems(4,5),unfolded this] Suc.prems(3) have j:"j < n (i - 1 - 1)" by auto
  have *:"\<And> c d e x. smult c d = e \<Longrightarrow> smult (x * c) d = smult x e" by auto
  have **:"\<And> c d e x. smult c d = e \<Longrightarrow> smult c (smult x d) = smult x e" by (auto simp:mult.commute)
  show ?case unfolding prod_list_map_remove1[OF inset(1),unfolded r1]
      *[OF Suc.hyps(1)[OF prems(1-3) j]]
      **[OF BT_lemma_2_21[OF prems(2,6) Suc.prems(3)]]
      by (auto simp: numeral_2_eq_2 ac_simps)
qed auto

lemma nonzero_alphaprod: assumes "i \<le> k + 1" shows "(\<Prod>l\<leftarrow>[3..<i]. \<alpha> l ^ (p l)) \<noteq> 0"
  unfolding prod_list_zero_iff using assms by (auto simp: \<alpha>0)

lemma BT_eq_30': assumes i: "3 \<le> i" "i \<le> k + 1" "j < n (i - 1)"
shows "subresultant j (F 1) (F 2)
  = smult ((- 1) ^ (\<Sum>l\<leftarrow>[3..<i]. (n (l - 2) - j) * (n (l - 1) - j))
     * (\<Prod>l\<leftarrow>[3..<i]. (\<beta> l / \<alpha> l) ^ (n (l - 1) - j)) * (\<Prod>l\<leftarrow>[3..<i]. f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1)))) (subresultant j (F (i - 2)) (F (i - 1)))"
  (is "_ = smult (?mm * ?b * ?f) _")
proof -
  let ?a = "\<Prod>l\<leftarrow>[3..<i]. \<alpha> l ^ (n (l - 1) - j)"
  let ?d = "\<Prod>l\<leftarrow>[3..<i]. \<beta> l ^ (n (l - 1) - j) * f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1)) *
                     (- 1) ^ ((n (l - 2) - j) * (n (l - 1) - j))"
  let ?m = "\<Prod>l\<leftarrow>[3..<i]. (- 1) ^ ((n (l - 2) - j) * (n (l - 1) - j))"
  have a0: "?a \<noteq> 0" by (rule nonzero_alphaprod, rule i)
  with arg_cong[OF BT_eq_30[OF i], of "smult (inverse ?a)", unfolded smult_smult]
  have "subresultant j (F 1) (F 2) = smult (inverse ?a * ?d)
    (subresultant j (F (i - 2)) (F (i - 1)))"
    by simp
  also have "inverse ?a * ?d = ?b * ?f * ?m" unfolding prod_list_multf inverse_prod_list map_map o_def
      power_inverse[symmetric] power_mult_distrib divide_inverse_commute
    by simp
  also have "?m = ?mm"
    unfolding prod_list_minus_1_exp by simp
  finally show ?thesis by (simp add: ac_simps)
qed

text \<open>For defining the subresultant PRS, we mainly follow Brown's ``The Subresultant PRS Algorithm'' (B).\<close>

definition "R j = (if j = n 2 then sdiv_poly (smult ((lead_coeff G2)^(\<delta> 1)) G2) (lead_coeff G2) else subresultant j G1 G2)"

abbreviation "ff i \<equiv> to_fract (i :: 'a)"
abbreviation "ffp \<equiv> map_poly ff"

sublocale map_poly_hom: map_poly_inj_idom_hom to_fract..

(* for \<sigma> and \<tau> we only take additions, so that no negative number-problems occur *)
definition "\<sigma> i = (\<Sum>l\<leftarrow>[3..<Suc i]. (n (l - 2) + n (i - 1) + 1) * (n (l - 1) + n (i - 1) + 1))"
definition "\<tau> i = (\<Sum>l\<leftarrow>[3..<Suc i]. (n (l - 2) + n i) * (n (l - 1) + n i))"

definition "\<gamma> i = (-1)^(\<sigma> i) * pow_int ( f (i - 1)) (1 - int (\<delta> (i - 1))) * (\<Prod>l\<leftarrow>[3..<Suc i].
  (\<beta> l / \<alpha> l)^(n (l - 1) - n (i - 1) + 1) * (f (l - 1))^(\<delta> (l - 2) + \<delta> (l - 1)))"
definition "\<Theta> i = (-1)^(\<tau> i) * pow_int (f i) (int (\<delta> (i - 1)) - 1) * (\<Prod>l\<leftarrow>[3..<Suc i].
  (\<beta> l / \<alpha> l)^(n (l - 1) - n i) * (f (l - 1))^(\<delta> (l - 2) + \<delta> (l - 1)))"

(* is eq 29 in BT *)
lemma fundamental_theorem_eq_4: assumes i: "3 \<le> i" "i \<le> k"
  shows "ffp (R (n (i - 1) - 1)) = smult (\<gamma> i) (F i)"
proof -
  have "n (i - 1) \<le> n 2" by (rule n_ge_trans, insert i, auto)
  with n_gt[of "i - 1"] i have "n (i - 1) - 1 < n 2"
    and lt: "n (i - 1) - 1 < n (i - 1)" by linarith+
  hence "R (n (i - 1) - 1) = subresultant (n (i - 1) - 1) G1 G2"
    unfolding R_def by auto
  from arg_cong[OF this, of ffp, unfolded to_fract_hom.subresultant_hom, folded F1 F2]
  have id1: "ffp (R (n (i - 1) - 1)) = subresultant (n (i - 1) - 1) (F 1) (F 2)" .
  note eq_24 = BT_lemma_2_24[OF i]
  let ?o = "(- 1) :: 'a fract"
  let ?m1 = "(\<delta> (i - 2) + 1)"
  let ?d1 = "f (i - 1) ^ (\<delta> (i - 2) + 1) * \<beta> i"
  let ?c1 = "?o ^ ?m1  * ?d1"
  let ?c0 = "\<alpha> i"
  have "?c0 \<noteq> 0" using \<alpha>0[of i] i by auto
  with arg_cong[OF eq_24, of "smult (inverse ?c0)"]
  have id2: "subresultant (n (i - 1) - 1) (F (i - 2)) (F (i - 1)) =
     smult (inverse ?c0 * ?c1) (F i)"
    by (auto intro: poly_eqI)
  from i have "3 \<le> i" "i \<le> k + 1" by auto
  note id3 = BT_eq_30'[OF this lt]
  let ?f = "\<lambda> l. f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1))"
  let ?b = "\<lambda> l. (\<beta> l / \<alpha> l) ^ (n (l - 1) - (n (i - 1) - 1))"
  let ?b' = "\<lambda> l. (\<beta> l / \<alpha> l) ^ (n (l - 1) - n (i - 1) + 1)"
  let ?m = "\<lambda> l.  (n (l - 2) - (n (i - 1) - 1)) * (n (l - 1) - (n (i - 1) - 1))"
  let ?m' = "\<lambda> l. (n (l - 2) + n (i - 1) + 1) * (n (l - 1) + n (i - 1) + 1)"
  let ?m2 = "(\<Sum>l\<leftarrow>[3..<i]. ?m l)"
  let ?b2 = "(\<Prod>l\<leftarrow>[3..<i]. ?b l)"
  let ?f2 = "(\<Prod>l\<leftarrow>[3..<i]. ?f l)"
  let ?f1 = "pow_int ( f (i - 1)) (1 - int (\<delta> (i - 1)))"
  have id4: "\<gamma> i = ?o ^ (?m1 + ?m2) * (inverse ?c0 * ?d1 * ?b2 * ?f2)"
  proof -
    have id: "\<gamma> i = (-1)^(\<sigma> i) * (?f1 * (\<Prod>l\<leftarrow>[3..<Suc i]. ?b' l) * (\<Prod>l\<leftarrow>[3..<Suc i]. ?f l))"
      unfolding \<gamma>_def prod_list_multf by simp
    have cong: "even m1 = even m2 \<Longrightarrow> c1 = c2 \<Longrightarrow> ?o^m1 * c1 = ?o^m2 * c2" for m1 m2 c1 c2
      unfolding minus_1_power_even by auto
    show ?thesis unfolding id
    proof (rule cong)
      from n_gt[of "i - 1"] i have n1: "n (i - 1) \<noteq> 0" by linarith
      {
        fix l
        assume "2 \<le> l" "l \<le> i"
        hence l: "l \<ge> 2" "l - 1 \<le> i - 1" "l \<le> k" using i by auto
        from n_ge_trans[OF _ l(2)] l i have n2: "n (i - 1) \<le> n (l - 1)" by auto
        from n1 n2 have id: "n (l - 1) - (n (i - 1) - 1) = n (l - 1) - n (i - 1) + 1" by auto
        have "even (n (l - 1) - (n (i - 1) - 1)) = even (n (l - 1) + n (i - 1) + 1)"
          unfolding id using n2 by auto
        note id n2 this
      } note diff = this
      have f0: "f (i - 1) \<noteq> 0" using f0[of "i - 1"] i by auto
      have "(\<Prod>l\<leftarrow>[3..<Suc i]. ?b' l) = (\<Prod>l\<leftarrow>[3..<Suc i]. ?b l)"
        by (rule arg_cong, rule map_cong, use diff(1) in auto)
      also have "\<dots> = ?b2 * ?b i" using i by auto
      finally have "?f1 * (\<Prod>l\<leftarrow>[3..<Suc i]. ?b' l) * (\<Prod>l\<leftarrow>[3..<Suc i]. ?f l) =
         (?b2 * ?f2) * (?f1 * ?b i * ?f i)" using i by simp
      also have "?f1 * ?b i * ?f i = (?f1 * ?f i) * \<beta> i * inverse ?c0" using n1 by (simp add: divide_inverse)
      also have "?f1 * ?f i = f (i - 1) ^ (\<delta> (i - 2) + 1)"
        unfolding exp_pow_int pow_int_add[OF f0, symmetric] by simp
      finally
      show "?f1 * (\<Prod>l\<leftarrow>[3..<Suc i]. ?b' l) * (\<Prod>l\<leftarrow>[3..<Suc i]. ?f l)
         = inverse ?c0 * ?d1 * ?b2 * ?f2" by simp
      have "even (\<sigma> i) = even ((\<Sum>l\<leftarrow>[3..<i]. ?m' l) + ?m' i)" unfolding \<sigma>_def using i by simp
      also have "\<dots> = (even (\<Sum>l\<leftarrow>[3..<i]. ?m' l) = even (?m' i))" by simp
      also have "even (\<Sum>l\<leftarrow>[3..<i]. ?m' l) = even ?m2"
      proof (rule even_sum_list, goal_cases)
        case (1 l)
        hence l: "l \<ge> 2" "l \<le> i" and l1: "l - 1 \<ge> 2" "l - 1 \<le> i" by auto
        have l2: "l - 2 = l - 1 - 1" by simp
        show ?case using diff(3) [OF l] diff(3) [OF l1] l2
          by auto
      qed
      also have "even (?m' i) = even ?m1"
      proof -
        from i have id: "Suc (i - 1 - 1) = i - 1" "i - 2 = i - 1 - 1" by auto
        have "even ?m1 = even (n (i - 2) + n (i - 1) + 1)" unfolding \<delta> id
          using diff[of "i - 1"] i by auto
        also have "\<dots> = even (?m' i)" by auto
        finally show ?thesis by simp
      qed
      also have "(even ?m2 = even ?m1) = even (?m2 + ?m1)" unfolding even_add by simp
      also have "?m2 + ?m1 = ?m1 + ?m2" by simp
      finally show "even (\<sigma> i) = even (?m1 + ?m2)" .
    qed
  qed
  show ?thesis unfolding id1 id3 id2 smult_smult id4 by (simp add: ac_simps power_add)
qed

(* equation 28 in BT *)
lemma fundamental_theorem_eq_5: assumes i: "3 \<le> i" "i \<le> k" "n i < j" "j < n (i - 1) - 1"
  shows "R j = 0"
proof -
  from BT_lemma_2_23[OF i] have id1: "subresultant j (F (i - 2)) (F (i - 1)) = 0" .
  have "n (i - 1) \<le> n 2" by (rule n_ge_trans, insert i, auto)
  with n_gt[of "i - 1"] i have "n (i - 1) - 1 < n 2"
    and lt: "j < n (i - 1)" by linarith+
  with i have "R j = subresultant j G1 G2" unfolding R_def by auto
  from arg_cong[OF this, of ffp, unfolded to_fract_hom.subresultant_hom, folded F1 F2]
  have id2: "ffp (R j) = subresultant j (F 1) (F 2)" .
  from i have "3 \<le> i" "i \<le> k + 1" by auto
  note eq_30 = BT_eq_30[OF this lt]
  let ?c3 = "\<Prod>l\<leftarrow>[3..<i]. \<alpha> l ^ (n (l - 1) - j)"
  let ?c2 = "\<Prod>l\<leftarrow>[3..<i]. \<beta> l ^ (n (l - 1) - j) * f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1)) *
                  (- 1) ^ ((n (l - 2) - j) * (n (l - 1) - j))"
  have "?c3 \<noteq> 0" by (rule nonzero_alphaprod, insert i, auto)
  with arg_cong[OF eq_30, of "smult (inverse ?c3)"]
  have id3: "subresultant j (F 1) (F 2) = smult (inverse ?c3 * ?c2)
     (subresultant j (F (i - 2)) (F (i - 1)))"
    by (auto intro: poly_eqI)
  have "ffp (R j) = 0" unfolding id1 id2 id3 by simp
  thus ?thesis by simp
qed

(* equation 27 in BT *)
lemma fundamental_theorem_eq_6: assumes "3 \<le> i" "i \<le> k" shows "ffp (R (n i)) = smult (\<Theta> i) (F i)"
  (is "?lhs=?rhs")
proof -
  from assms have i1:"1 \<le> i" by auto
  from assms have nlt:"i \<le> k + 1" "n i < n (i - 1)" using n_gt[of "i - 1"] by auto
  from assms have \<alpha>nz:"\<alpha> i ^ \<delta> (i - 1) \<noteq> 0" using \<alpha>0 by auto
  have *:"\<And> a f b. a \<noteq> 0 \<Longrightarrow> smult a f = b \<Longrightarrow> f = smult (inverse (a::'a fract)) b" by auto
  have **:"\<And> f g xs c. c * prod_list (map f xs) * prod_list (map g xs)
         = c * (\<Prod>x\<leftarrow>xs. f x * (g:: _ \<Rightarrow> (_ :: comm_monoid_mult)) x)"
         by (auto simp:ac_simps prod_list_multf)
  have ***:"\<And> c. \<beta> i ^ \<delta> (i - Suc 0) * (inverse (\<alpha> i ^ \<delta> (i - Suc 0)) * c) = (\<beta> i / \<alpha> i) ^ \<delta> (i - 1) * c"
    by (auto simp:inverse_eq_divide power_divide)
  have ****:"int (n (i - Suc 0) - n i) - 1 = int (n (i - 1) - Suc (n i))"
    using assms nlt by auto
  from assms n_ge[of "i-2"] nlt n_ge[of i]
    have nge:"n (i - Suc 0) \<le> n (i - 2)" "n i < n (i - Suc 0)" "n i < n (i - 1)" "Suc (i - 2) = i - 1"
    by (cases i,auto simp:numeral_2_eq_2 numeral_3_eq_3)
  have *****:"(- 1 ::  'a fract) ^ ((n (i - Suc 0) - n i) * (n (i - Suc 0) - n i + (n (i - 2) - n (Suc (i - 2)))))
       = (- 1) ^ ((n i + n (i - Suc 0)) * (n i + n (i - 2)))"
       "(- 1 ::  'a fract) ^ (\<Sum>l\<leftarrow>[3..<i]. (n (l - Suc 0) - n i) * (n (l - 2) - n i))
       = (- 1) ^ (\<Sum>l\<leftarrow>[3..<i]. (n i + n (l - Suc 0)) * (n i + n (l - 2))) "
    using nge apply (intro minus_1_even_eqI,auto)
    apply (intro minus_1_even_eqI)
    apply (intro even_sum_list)
    proof(goal_cases) case (1 x)
      with n_ge_trans assms
        have "n i \<le> n (x - Suc 0)" "n (x - 2) \<ge> n i" by auto
      with 1 show ?case by auto
    qed
  have "ffp (R (n i)) = subresultant (n i) (F 1) (F 2)" unfolding R_def F1 F2
    by (auto simp: to_fract_hom.subresultant_hom ni2[OF assms])
  also have "\<dots> = smult
     ((- 1) ^ (\<Sum>l\<leftarrow>[3..<i]. (n (l - 2) - n i) * (n (l - 1) - n i)) *
      (\<Prod>x\<leftarrow>[3..<i]. (\<beta> x / \<alpha> x) ^ (n (x - 1) - n i) * f (x - 1) ^ (\<delta> (x - 1) + \<delta> (x - 2))) *
      (((\<beta> i / \<alpha> i) ^ \<delta> (i - 1)) * f (i - 1) ^ (\<delta> (i - 1) + \<delta> (i - 2))) *
       ((- 1) ^ ((\<delta> (i - 2) + \<delta> (i - 1)) * \<delta> (i - 1)) * f i ^ (\<delta> (i - 1) - 1)
        ))
     (F i)"
    unfolding BT_eq_30'[OF assms(1) nlt] **
              *[OF \<alpha>nz BT_lemma_2_22[OF assms]] smult_smult by (auto simp:ac_simps *** )
  also have "\<dots> = ?rhs" unfolding \<Theta>_def \<tau>_def
    using prod_combine[OF assms(1)] \<delta> assms
    by (auto simp:ac_simps exp_pow_int[symmetric] power_add ***** ****)
  finally show ?thesis.
qed

(* equation 26 in BT *)
lemma fundamental_theorem_eq_7: assumes j: "j < n k" shows "R j = 0"
proof -
  let ?P = "pseudo_divmod (F (k - 1)) (F k)"
  from F0[of k] k2 have Fk: "F k \<noteq> 0" by auto
  from pmod[of "Suc k"] k2 F0[of "Suc k"]
  have "pseudo_mod (F (k - 1)) (F k) = 0" by auto
  then obtain Q where "?P = (Q,0)"
    unfolding pseudo_mod_def by (cases ?P, auto)
  from pseudo_divmod(1)[OF Fk this] Fk obtain c where id: "smult c (F (k - 1)) = F k * Q"
    and c: "c \<noteq> 0" by auto
  from id have id: "smult c (F (k - 1)) = Q * F k" by auto
  from n_ge[unfolded n, of "k - 1"] k2 c have "degree (F k) \<le> degree (smult c (F (k - 1)))" by auto
  from subresultant_product[OF id this, unfolded subresultant_smult_left[OF c], of j] j
  have *:"subresultant j (F (k + 1 - 2)) (F (k + 1 - 1)) = 0" using c unfolding n by simp
  from assms have **:"j \<noteq> n 2"
    by (meson k2 n_ge_trans not_le one_le_numeral order_refl)
  from k2 assms have "3 \<le> k + 1" "k + 1 \<le> k + 1" "j < n (k + 1 - 1)" by auto
  from BT_eq_30[OF this,unfolded *] nonzero_alphaprod[OF le_refl] ** F1 F2
  show ?thesis by (auto simp:R_def F0 to_fract_hom.subresultant_hom[symmetric])
qed


definition "G i = R (n (i - 1) - 1)"
definition "H i = R (n i)"

lemma gamma_delta_beta_3: "\<gamma> 3 = (- 1) ^ (\<delta> 1 + 1) * \<beta> 3"
proof -
  have "\<gamma> 3 = (- 1) ^ \<sigma> 3 * pow_int (f 2) (1 - int (\<delta> 2)) *
    (\<beta> 3 / (f 2 ^ Suc (\<delta> 1)) * f 2 ^ (\<delta> 1 + \<delta> 2))"
    unfolding \<gamma>_def \<delta> \<alpha>_def by (simp add: \<delta>)
  also have "f 2 ^ (\<delta> 1 + \<delta> 2) = pow_int (f 2) (int (\<delta> 1 + \<delta> 2))"
    unfolding pow_int_def nat_int by auto
  also have "int (\<delta> 1 + \<delta> 2) = int (Suc (\<delta> 1)) + (int (\<delta> 2) - 1)" by simp
  also have "pow_int (f 2) \<dots> = pow_int (f 2) (Suc (\<delta> 1)) * pow_int (f 2) (int (\<delta> 2) - 1)"
    by (rule pow_int_add, insert f20, auto)
  also have "pow_int (f 2) (Suc (\<delta> 1)) = f 2 ^ (Suc (\<delta> 1))" unfolding pow_int_def nat_int by simp
  also have "\<beta> 3 / (f 2 ^ Suc (\<delta> 1)) *
   (f 2 ^ Suc (\<delta> 1) * pow_int (f 2) (int (\<delta> 2) - 1))
    = (\<beta> 3 / (f 2 ^ Suc (\<delta> 1)) *  f 2 ^ Suc (\<delta> 1) * pow_int (f 2) (int (\<delta> 2) - 1))" by simp
  also have "\<beta> 3 / (f 2 ^ Suc (\<delta> 1)) * f 2 ^ Suc (\<delta> 1) = \<beta> 3" using f20 by auto
  finally have "\<gamma> 3 = ((- 1) ^ \<sigma> 3 * \<beta> 3) * (pow_int (f 2) (1 - int (\<delta> 2)) * pow_int (f 2) (int (\<delta> 2) - 1))"
    by simp
  also have "pow_int (f 2) (1 - int (\<delta> 2)) * pow_int (f 2) (int (\<delta> 2) - 1)
    = 1"
    by (subst pow_int_add[symmetric], insert f20, auto)
  finally have "\<gamma> 3 = (- 1) ^ \<sigma> 3 * \<beta> 3" by simp
  also have "\<sigma> 3 = (n 1 + n 2 + 1) * (n 2 + n 2 + 1)" unfolding \<sigma>_def
    by simp
  also have "(- (1 :: 'a fract)) ^ \<dots> = (- 1) ^ (n 1 - n 2 + 1)"
    by (rule minus_1_even_eqI, insert n12, auto)
  also have "\<dots> = (- 1)^(\<delta> 1 + 1)" unfolding \<delta> by (simp add: numeral_2_eq_2)
  finally show "\<gamma> 3 = (- 1) ^ (\<delta> 1 + 1) * \<beta> 3" .
qed

fun h :: "nat \<Rightarrow> 'a fract" where
  "h i = (if (i \<le> 1) then 1 else if i = 2 then (f 2 ^ \<delta> 1) else (f i ^ \<delta> (i - 1) / (h (i - 1) ^ (\<delta> (i - 1) - 1))))"

lemma smult_inverse_sdiv_poly: assumes ffp: "p \<in> range ffp"
  and p: "p = smult (inverse x) q"
  and p': "p' = sdiv_poly q' x'"
  and xx: "x = ff x'"
  and qq: "q = ffp q'"
shows "p = ffp p'"
proof (rule poly_eqI)
  fix i
  have "coeff p i = coeff q i / x" unfolding p by (simp add: field_simps)
  also have "\<dots> = ff (coeff q' i) / ff x'" unfolding qq xx by simp
  finally have cpi: "coeff p i = ff (coeff q' i) / ff x'" .
  from ffp obtain r where pr: "p = ffp r" by auto
  from arg_cong[OF this, of "\<lambda> p. coeff p i", unfolded cpi]
  have "ff (coeff q' i) / ff x' \<in> range ff" by auto
  hence id: "ff (coeff q' i) / ff x' = ff (coeff q' i div x')"
    by (rule div_divide_to_fract, auto)
  show "coeff p i = coeff (ffp p') i" unfolding cpi id p'
    by (simp add: sdiv_poly_def coeff_map_poly)
qed

end

locale subresultant_prs_locale2 = subresultant_prs_locale F n \<delta> f k \<beta> G1 G2 for
       F :: "nat \<Rightarrow> 'a :: idom_divide fract poly"
    and n :: "nat \<Rightarrow> nat"
    and \<delta> :: "nat \<Rightarrow> nat"
    and f :: "nat \<Rightarrow> 'a fract"
    and k :: nat
    and \<beta> :: "nat \<Rightarrow> 'a fract"
    and G1 G2 :: "'a poly" +
  assumes \<beta>3: "\<beta> 3 = (-1)^(\<delta> 1 + 1)"
  and \<beta>i: "\<And> i. 4 \<le> i \<Longrightarrow> i \<le> Suc k \<Longrightarrow> \<beta> i = (-1)^(\<delta> (i - 2) + 1) * f (i - 2) * h (i - 2) ^ (\<delta> (i - 2))"
begin

lemma B_eq_17_main: "2 \<le> i \<Longrightarrow> i \<le> k \<Longrightarrow>
    h i = (-1) ^ (n 1 + n i + i + 1) / f i
   * (\<Prod>l\<leftarrow>[3..< Suc (Suc i)]. (\<alpha> l / \<beta> l)) \<and> h i \<noteq> 0"
proof (induct i rule: less_induct)
  case (less i)
  from less(2-) have fi0: "f i \<noteq> 0" using f0[of i] by simp
  have 1: "(- 1) \<noteq> (0 :: 'a fract)" by simp
  show ?case (is "h i = ?r i \<and> _")
  proof (cases "i = 2")
    case True
    have f20: "f 2 \<noteq> 0" using f20 by auto
    have hi: "h i = f 2 ^ \<delta> 1" unfolding True h.simps[of 2] by simp
    have id: "int (\<delta> 1) = int (n 1) - int (n 2)" using n12 unfolding \<delta> numeral_2_eq_2 by simp
    have "?r i = (- 1) ^ (1 + n 1 + n 2)
      * ((f 2 ^ Suc (\<delta> 1)) / (\<beta> 3)) / pow_int (f 2) 1" unfolding True \<alpha>_def by simp
    also have "\<beta> 3 = (- 1) ^ (\<delta> 1 + 1)" by (rule \<beta>3)
    also have "f 2 ^ Suc (\<delta> 1) / \<dots> = \<dots> * f 2 ^ Suc (\<delta> 1)" by simp
    finally have "?r i = ((- 1) ^ (1 + n 1 + n 2) * ((- 1) ^ (\<delta> 1 + 1))) *
        pow_int (f 2) (int (Suc (\<delta> 1)) + (-1))" (is "_ = ?a * _")
      unfolding pow_int_divide exp_pow_int power_add pow_int_add[OF f20] by (simp add: ac_simps pow_int_add)
    also have "?a = (-1)^(1 + n 1 + n 2 + \<delta> 1 + 1)" unfolding power_add by simp
    also have "\<dots> = (-1)^0"
      by (rule minus_1_even_eqI, insert n12, auto simp: \<delta> numeral_2_eq_2, presburger)
    finally have ri: "?r i = pow_int (f 2) (int (\<delta> 1))" by simp
    show ?thesis unfolding ri hi exp_pow_int[symmetric] using f20 by simp
  next
    case False
    hence i: "i \<ge> 3" and ii: "i - 1 < i" "2 \<le> i - 1" "i - 1 \<le> k" using less(2-) by auto
    from i less(2-) have cc: "4 \<le> Suc i" "Suc i \<le> Suc k" by auto
    define P where "P = (\<Prod>l\<leftarrow>[3..< Suc i]. \<alpha> l / \<beta> l)"
    define Q where "Q = P * pow_int (h (i - 1)) (- int (\<delta> (i - 1)))"
    define R where "R = f i ^ \<delta> (i - 1)"
    define S where "S = pow_int (f (i - 1)) (- 1)"
    note IH = less(1)[OF ii]
    hence hi0: "h (i - 1) \<noteq> 0" by auto
    have hii: "h i = f i ^ \<delta> (i - 1) / h (i - 1) ^ (\<delta> (i - 1) - 1)"
      unfolding h.simps[of i] using i by simp
    also have "\<dots> = f i ^ \<delta> (i - 1) * pow_int (h (i - 1)) (- int (\<delta> (i - 1) - 1))"
      unfolding exp_pow_int pow_int_divide by simp
    also have "int (\<delta> (i - 1) - 1) = int (\<delta> (i - 1)) - 1"
    proof -
      have "\<delta> (i - 1) > 0" unfolding \<delta>[of "i - 1"] using n_gt[OF ii(2)] less(2-) by auto
      thus ?thesis by simp
    qed
    also have "- (int (\<delta> (i - 1)) - 1) = 1 + (- int (\<delta> (i - 1)))" by simp
    finally have hi: "h i = (- 1) ^ (n 1 + n (i - 1) + i) * (R * Q * S)"
      unfolding pow_int_add[OF hi0] P_def Q_def pow_int_divide[symmetric] R_def S_def using IH i by (simp add: ac_simps)
    from i have id: "[3..<Suc (Suc i)] = [3 ..< Suc i] @ [Suc i]" by simp
    have "?r i = (- 1) ^ (n 1 + n i + i + 1)
      * pow_int (f i) (- 1) * P * \<alpha> (Suc i) / \<beta> (Suc i)"
      unfolding pow_int_divide[symmetric] P_def id Fract_conv_to_fract by simp
    also have "\<beta> (Suc i) = (- 1) ^ (\<delta> (i - 1) + 1) * f (i - 1) * h (i - 1) ^ \<delta> (i - 1)"
      using \<beta>i[OF cc] by simp
    also have "\<alpha> (Suc i) = f i ^ Suc (\<delta> (i - 1))" unfolding \<alpha>_def by simp
    finally have "?r i = (- 1) ^ (n 1 + n i + i + 1) * pow_int (f i) (- 1) * P *  (f i ^ Suc (\<delta> (i - 1))) /
      (- 1) ^ (\<delta> (i - 1) + 1) * pow_int (f (i - 1)) (- 1) / h (i - 1) ^ \<delta> (i - 1)"
      (is "_ = ?a1 * ?fi1 * P * ?fi2 / ?a2 * ?b / ?c")
      unfolding exp_pow_int pow_int_divide[symmetric] by simp
    also have "\<dots> = (?a1 / ?a2) * (?fi1 * ?fi2) * (P / ?c) * ?b" by (simp add: ac_simps)
    also have "?a1 / ?a2 = (- 1) ^ (n 1 + n i + i + 1 + \<delta> (i - 1) + 1)"
      by (simp add: power_add)
    also have "\<dots> = (-1) ^ (n 1 + n i + i + \<delta> (i - 1))"
      by (rule minus_1_even_eqI, auto)
    also have "n 1 + n i + i + \<delta> (i - 1) = n 1 + n (i - 1) + i"
      unfolding \<delta> using i less(2-) n_ge[of "i - 1"] by simp
    also have "?fi1 * ?fi2 = pow_int (f i) (-1 + int (Suc (\<delta> (i - 1))))"
      unfolding exp_pow_int pow_int_add[OF fi0] by simp
    also have "\<dots> = pow_int (f i) (int (\<delta> (i - 1)))" by simp
    also have "P / ?c = Q"  unfolding Q_def exp_pow_int pow_int_divide by simp
    also have "?b = S" unfolding S_def by simp
    finally have ri: "?r i = (-1)^(n 1 + n (i - 1) + i)
      * (R * Q * S)" by (simp add: exp_pow_int R_def)
    have id: "h i = ?r i" unfolding hi ri ..
    show ?thesis
      by (rule conjI[OF id], unfold hii, insert IH fi0, auto)
  qed
qed

lemma B_eq_17: "2 \<le> i \<Longrightarrow> i \<le> k \<Longrightarrow>
    h i = (-1) ^ (n 1 + n i + i + 1) / f i * (\<Prod>l\<leftarrow>[3..< Suc (Suc i)]. (\<alpha> l / \<beta> l))"
  using B_eq_17_main by blast

lemma B_theorem_2: "3 \<le> i \<Longrightarrow> i \<le> Suc k \<Longrightarrow> \<gamma> i = 1"
proof (induct i rule: less_induct)
  case (less i)
  show ?case
  proof (cases "i = 3")
    case True
    show ?thesis unfolding True unfolding gamma_delta_beta_3 \<beta>3 by simp
  next
    case False
    with less(2-)
    have i: "i \<ge> 4" and ii: "i - 1 < i" "3 \<le> i - 1" "i - 1 \<le> Suc k"
      and iii: "4 \<le> i" "i \<le> Suc k"
      and iv: "2 \<le> i - 2" "i - 2 \<le> k" by auto
    from less(1)[OF ii] have IH: "\<gamma> (i - 1) = 1" .
    define L where "L = [3..< i]"
    have id: "[3..<Suc (i - 1)] = L" "[3..<Suc i] = L @ [i]" "Suc (Suc (i - 2)) = i"
      unfolding L_def using i by auto
    define B where "B = (\<lambda> l. \<beta> l / \<alpha> l)"
    define A where "A = (\<lambda> l. \<alpha> l / \<beta> l)"
    define Q where "Q = (\<lambda> l. f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1)))"
    define R where "R = (\<lambda> i l. B l ^ (n (l - 1) - n (i - 1) + 1))"
    define P where "P = (\<lambda> i l. R i l * Q l)"
    have fi0: "f (i - 1) \<noteq> 0" using f0[of "i - 1"] less(2-) by auto
    have fi0': "f (i - 2) \<noteq> 0" using f0[of "i - 2"] less(2-) by auto
    {
      fix j
      assume "j \<in> set L"
      hence "j \<ge> 3" "j < i" unfolding L_def by auto
      with less(3) have j: "j - 1 \<noteq> 0" "j - 1 < k" by auto
      hence Q: "Q j \<noteq> 0" unfolding Q_def using f0[of "j - 1"] by auto
      from j \<alpha>0 \<beta>0[of j] have 0: "\<alpha> j \<noteq> 0" "\<beta> j \<noteq> 0" by auto
      hence "B j \<noteq> 0" "A j \<noteq> 0" unfolding B_def A_def by auto
      note Q this
    } note L0 = this
    let ?exp = "\<delta> (i - 2)"
    have "\<gamma> i = \<gamma> i / \<gamma> (i - 1)" unfolding IH by simp
    also have "\<dots> = (- 1) ^ \<sigma> i * pow_int (f (i - 1)) (1 - int (\<delta> (i - 1))) *
      (\<Prod>l\<leftarrow>L. P i l) * P i i /
      ((- 1) ^ \<sigma> (i - 1) * pow_int (f (i - 2)) (1 - int (\<delta> (i - 2))) *
       (\<Prod>l\<leftarrow>L. P (i - 1) l))"  (is "_ = ?a1 * ?f1 * ?L1 * P i i / (?a2 * ?f2 * ?L2)")
      unfolding \<gamma>_def id P_def Q_def R_def B_def by (simp add: numeral_2_eq_2)
    also have "\<dots> = (?a1 * ?a2) * (?f1 * P i i) / ?f2 * (?L1 / ?L2)" unfolding divide_prod_assoc by simp
    also have "?a1 * ?a2 = (-1)^(\<sigma> i + \<sigma> (i - 1))" (is "_ = ?a") unfolding power_add by simp
    also have "?L1 / ?L2 = (\<Prod>l\<leftarrow>L. R i l) / (\<Prod>l\<leftarrow>L. R (i - 1) l) * ((\<Prod>l\<leftarrow>L. Q l) / (\<Prod>l\<leftarrow>L. Q l))"
      unfolding P_def prod_list_multf divide_prod_assoc by simp
    also have "\<dots> = (\<Prod>l\<leftarrow>L. R i l) / (\<Prod>l\<leftarrow>L. R (i - 1) l)" (is "_ = ?L1 / ?L2")
    proof -
      have "(\<Prod>l\<leftarrow>L. Q l) \<noteq> 0" unfolding prod_list_zero_iff using L0 by auto
      thus ?thesis by simp
    qed
    also have "?f1 * P i i = (?f1 * pow_int (f (i - 1)) (int ?exp + int (\<delta> (i - 1)))) * R i i" unfolding P_def Q_def
      exp_pow_int by simp
    also have "?f1 * pow_int (f (i - 1)) (int ?exp + \<delta> (i - 1)) = pow_int (f (i - 1))
      (1 + int ?exp)" (is "_ = ?f1")
      unfolding pow_int_add[OF fi0, symmetric] by simp
    also have "R i i = \<beta> i / \<alpha> i" unfolding B_def R_def Fract_conv_to_fract by simp
    also have "\<alpha> i = f (i - 1) ^ Suc ?exp" unfolding \<alpha>_def by simp
    also have "\<beta> i / \<dots> = \<beta> i * pow_int (f (i - 1)) (- 1 - ?exp)"
      (is "_ = ?\<beta> * ?f12")
      unfolding exp_pow_int pow_int_divide by simp
    finally have "\<gamma> i = (?a * (?f1 * ?f12)) *  ?\<beta> / ?f2 * (?L1 / ?L2)"
      by simp
    also have "?a * (?f1 * ?f12) = ?a" unfolding pow_int_add[OF fi0, symmetric] by simp
    also have "?L1 / ?L2 = pow_int (\<Prod>l\<leftarrow>L. A l) (- ?exp)"
    proof -
      have id: "i - 1 - 1 = i - 2" by simp
      have "set L \<subseteq> {l. 3 \<le> l \<and> l \<le> k \<and> l < i}" unfolding L_def using less(3) by auto
      thus ?thesis unfolding R_def id
      proof (induct L)
        case (Cons l L)
        from Cons(2) have l: "3 \<le> l" "l \<le> k" "l < i" and L: "set L \<subseteq> {l. 3 \<le> l \<and> l \<le> k \<and> l < i}" by auto
        note IH = Cons(1)[OF L]
        from l \<alpha>0 \<beta>0[of l] have 0: "\<alpha> l \<noteq> 0" "\<beta> l \<noteq> 0" by auto
        hence B0: "B l \<noteq> 0" unfolding B_def by auto
        have "(\<Prod>l\<leftarrow>l # L. B l ^ (n (l - 1) - n (i - 1) + 1)) / (\<Prod>l\<leftarrow>l # L. B l ^ (n (l - 1) - n (i - 2) + 1))
          = (B l ^ (n (l - 1) - n (i - 1) + 1) * (\<Prod>l\<leftarrow>L. B l ^ (n (l - 1) - n (i - 1) + 1))) /
            (B l ^ (n (l - 1) - n (i - 2) + 1) * (\<Prod>l\<leftarrow>L. B l ^ (n (l - 1) - n (i - 2) + 1)))"
          (is "_ = (?l1 * ?L1) / (?l2 * ?L2)") by simp
        also have "\<dots> = (?l1 / ?l2) * (?L1 / ?L2)" by simp
        also have "?L1 / ?L2 = pow_int (prod_list (map A L)) (- int (\<delta> (i - 2)))" by (rule IH)
        also have "?l1 / ?l2 = pow_int (B l) (int (n (l - 1) - n (i - 1)) - int (n (l - 1) - n (i - 2)))" unfolding exp_pow_int pow_int_divide pow_int_add[OF B0, symmetric]
          by simp
        also have "int (n (l - 1) - n (i - 1)) - int (n (l - 1) - n (i - 2)) = int ?exp"
        proof -
          have "n (l - 1) \<ge> n (i - 2)" "n (l - 1) \<ge> n (i - 1)" "n (i - 2) \<ge> n (i - 1)"
            using i l less(3)
            by (intro n_ge_trans, auto)+
          hence id: "int (n (l - 1) - n (i - 1)) = int (n (l - 1)) - int (n (i - 1))"
                "int (n (l - 1) - n (i - 2)) = int (n (l - 1)) - int (n (i - 2))"
                "int (n (i - 2) - n (i - 1)) = int (n (i - 2)) - int (n (i - 1))"
            by simp_all
          have id2: "int ?exp = int (n (i - 2) - n (i - 1))"
            unfolding \<delta> using i by (cases i; cases "i - 1", auto)
          show ?thesis unfolding id2 unfolding id by simp
        qed
        also have "pow_int (B l) \<dots> = pow_int (inverse (B l)) (- \<dots>)" unfolding pow_int_def
          by (cases "int (\<delta> (i - 2))" rule: linorder_cases, auto simp: field_simps)
        also have "inverse (B l) = A l" unfolding B_def A_def by simp
        also have "pow_int (A l) (- int ?exp) * pow_int (prod_list (map A L)) (- int ?exp)
          = pow_int (prod_list (map A (l # L))) (- int ?exp)"
          by (simp add: pow_int_mult)
        finally show ?case .
      qed simp
    qed
    also have "\<beta> i = (- 1) ^ (?exp + 1) * f (i - 2) * h (i - 2) ^ ?exp"
      unfolding \<beta>i[OF iii] ..
    finally have "\<gamma> i =  (((- 1) ^ (\<sigma> i + \<sigma> (i - 1)) * (- 1) ^ (?exp + 1))) *
      (pow_int (f (i - 2)) 1 *
      pow_int (f (i - 2)) (int ?exp - 1)) *
      h (i - 2) ^ ?exp /
      (\<Prod>l\<leftarrow>L. A l) ^ ?exp" (is "_ = ?a * ?f1 * ?H / ?L") unfolding pow_int_divide exp_pow_int by simp
    also have "?f1 = pow_int (f (i - 2)) (int ?exp)" (is "_ = ?f1") unfolding pow_int_add[OF fi0', symmetric]
      by simp
    also have "h (i - 2) = (- 1) ^ (n 1 + n (i - 2) + (i - 2) + 1) / f (i - 2) *
      (\<Prod>l\<leftarrow>L. A l)" (is "_ = ?a2 / ?f2 * ?L") unfolding B_eq_17[OF iv] A_def id L_def by simp
    also have "((- (1 :: 'a fract)) ^ (\<sigma> i + \<sigma> (i - 1)) * (- 1) ^ (?exp + 1)) =
      ((- 1) ^ (\<sigma> i + \<sigma> (i - 1) + ?exp + 1))" (is "_ = ?a1") by (simp add: power_add)
    finally have "\<gamma> i = ?a1 * ?f1 * (?a2 / ?f2 * ?L) ^ ?exp / ?L ^ ?exp" by simp
    also have "\<dots> = (?a1 * ?a2^?exp) * (?f1 / ?f2 ^ ?exp) * (?L^?exp / ?L ^ ?exp)"
      unfolding power_mult_distrib power_divide by auto
    also have " ?L ^ ?exp / ?L ^ ?exp = 1"
    proof -
      have "?L \<noteq> 0" unfolding prod_list_zero_iff using L0 by auto
      thus ?thesis by simp
    qed
    also have "?f1 / ?f2 ^ ?exp = 1" unfolding exp_pow_int pow_int_divide
      pow_int_add[OF fi0', symmetric] by simp
    also have "?a2^?exp = (- 1) ^ ((n 1 + n (i - 2) + (i - 2) + 1) * ?exp)"
      by (rule semiring_normalization_rules)
    also have "?a1 * \<dots> = (- 1) ^ (\<sigma> i + \<sigma> (i - 1) + ?exp + 1 + (n 1 + n (i - 2) + (i - 2) + 1) * ?exp)"
      (is "_ = _ ^ ?e")
      by (simp add: power_add)
    also have "\<dots> = (-1)^0"
    proof -
      define e where "e = ?e"
      have *: "?e = (2 * ?exp + \<sigma> i + \<sigma> (i - 1) + 1 + (n 1 + n (i - 2) + (i - 2)) * ?exp)" by simp
      define A where "A = (\<lambda> i l. (n (l - 2) + n (i - 1) + 1) * (n (l - 1) + n (i - 1) + 1))"
      define B where "B = (\<lambda> i. (n (i - 1) + 1) * (n (i - 1) + 1))"
      define C where "C = (\<lambda> l. (n (l - 1) + n (l - 2) + n (l - 1) * n (l - 2)))"
      define D where "D = (\<lambda> l. n (l - 1) + n (l - 2))"
      define m2 where "m2 = n (i - 2)"
      define m1 where "m1 = n (i - 1)"
      define m0 where "m0 = n 1"
      define i3 where "i3 = i - 3"
      have m12: "m2 \<ge> m1" unfolding m2_def m1_def using n_ge[of "i - 2"] i less(3)
        by (cases i, auto)
      have idd: "Suc (i - 2) = i - 1" "i - 1 - 1 = i - 2" using i by auto
      have id4: "i - 2 = Suc i3" unfolding i3_def using i by auto
      from i have "3 < i" by auto
      hence "\<exists> k. sum_list (map D L) = n 1 + n (i - 2) + 2 * k" unfolding L_def
      proof (induct i rule: less_induct)
        case (less i)
        show ?case
        proof (cases "i = 4")
          case True
          thus ?thesis by (simp add: D_def)
        next
          case False
          obtain ii where i: "i = Suc ii" and ii: "ii < i" "3 < ii" using False less(2) by (cases i, auto)
          from less(1)[OF ii] obtain k where IH: "sum_list (map D [3 ..< ii]) = n 1 + n (ii - 2) + 2 * k" by auto
          have "map D [3 ..< i] = map D [3 ..< ii] @ [D ii]" unfolding i using ii by auto
          hence "sum_list (map D [3..<i]) = n 1 + n (ii - 2) + 2 * k + D ii" using IH by simp
          also have "\<dots> = n 1 + n (ii - 1) + 2 * (n (ii - 2) + k)" unfolding D_def by simp
          also have "n (ii - 1) = n (i - 2)" unfolding i by simp
          finally show ?thesis by blast
        qed
      qed
      then obtain kk where DL: "sum_list (map D L) = n 1 + n (i - 2) + 2 * kk" ..
      let ?l = "i - 3"
      have len: "length L = i - 3" unfolding L_def using i by auto
      have A: "A i l = B i + D l * n (i - 1) + C l" for i l
        unfolding A_def B_def C_def D_def ring_distribs by simp
      have id2: "[3..<Suc i] = 3 # [Suc 3 ..< Suc i]"
        unfolding L_def using i by (auto simp: upt_rec[of 3])
      have "even e = even ?e" unfolding e_def by simp
      also have "\<dots> = even ((1 + (n 1 + n (i - 2) + (i - 2)) * ?exp) + (\<sigma> i + \<sigma> (i - 1)))"
        (is "_ = even (?g + ?j)")
        unfolding * by (simp add: ac_simps)
      also have "?j = (\<Sum>l\<leftarrow>L @ [i]. A i l) + (\<Sum>l\<leftarrow>L. A (i - 1) l)"
        unfolding \<sigma>_def id A_def by simp
      also have "\<dots> = 2 * (\<Sum>l\<leftarrow>L. C l) + (Suc ?l) * B i + (\<Sum>l\<leftarrow>L @ [i]. D l * n (i - 1)) + C i +
          ?l * B (i - 1) + (\<Sum>l\<leftarrow>L. D l * n (i - 1 - 1))"
        unfolding A sum_list_addf by (simp add: sum_list_triv len)
      also have "\<dots> = ((Suc ?l * B i + C i +
          ?l * B (i - 1) + D i * n (i - 1)) + ((\<Sum>l\<leftarrow>L. D l) * (n (i - 1) + n (i - 2)) + 2 * (\<Sum>l\<leftarrow>L. C l)))"
        (is "_ = ?i + ?j")
        unfolding sum_list_mult_const by (simp add: ring_distribs numeral_2_eq_2)
      also have "?j =
          (n 1 + n (i - 2)) * (n (i - 1) + n (i - 2)) + 2 * (kk * (n (i - 1) + n (i - 2)) + (\<Sum>l\<leftarrow>L. C l))"
        (is "_ = ?h + 2 * ?f")
        unfolding DL by (simp add: ring_distribs)
      finally have "even e = even (?g + ?i + ?h + 2 * ?f)" by presburger
      also have "\<dots> = even (?g + ?i + ?h)" by presburger
      also have "?g + ?i + ?h =
         i3 * (m2 - m1 + m1 * m1 + m2 * m2)
         + (m2 - m1 + m1 + m2) * (m0 + m2)
         + (m1 + m2 + (m2 - m1))
         + 2 * (m1 * m2 + m1 * m1 + 1 + i3 + m1 * Suc i3 + m2 * i3)" unfolding idd B_def D_def C_def \<delta>
        m1_def[symmetric] m2_def[symmetric] m0_def[symmetric]
        unfolding i3_def[symmetric] id4
        by (simp add: ring_distribs)
      also have "(m1 + m2 + (m2 - m1)) = 2 * m2" using m12 by simp
      also have "(m2 - m1 + m1 + m2) * (m0 + m2) = 2 * (m2 * (m0 + m2))" using m12 by simp
      finally obtain l1 l2 l3 where
        "even e = even (i3 * (m2 - m1 + m1 * m1 + m2 * m2)  + 2 * l1 + 2 * l2 + 2 * l3)"
        by blast
      also have "\<dots> = even (i3 * (m2 - m1 + m1 * m1 + m2 * m2))" by simp
      also have "\<dots> = even (i3 * (2 * m1 + (m2 - m1 + m1 * m1 + m2 * m2)))" by simp
      also have "2 * m1 + (m2 - m1 + m1 * m1 + m2 * m2) = m1 + m2 + m1 * m1 + m2 * m2"
        using m12 by simp
      also have "even (i3 * \<dots>)" by auto
      finally have "even e" .
      thus ?thesis unfolding e_def
        by (intro minus_1_even_eqI, auto)
    qed
    finally show "\<gamma> i = 1" by simp
  qed
qed

context
  fixes i :: nat
  assumes i: "3 \<le> i" "i \<le> k"
begin
lemma B_theorem_3_b: "\<Theta> i * f i = ff (lead_coeff (H i))"
  using arg_cong[OF fundamental_theorem_eq_6[folded H_def, OF i], of lead_coeff] unfolding f[of i]
  lead_coeff_smult by simp

lemma B_theorem_3_main: "\<Theta> i * f i / \<gamma> (i + 1) = (-1)^(n 1 + n i + i + 1) / f i * (\<Prod>l\<leftarrow>[3..< Suc (Suc i)]. (\<alpha> l / \<beta> l))"
proof (cases "f i = 0")
  case True
  thus ?thesis by simp
next
  case False note ff0 = this
  from i(1) have "Suc (Suc i) > 3" by auto
  hence id: "[3 ..< Suc (i + 1)] = [3 ..< Suc i] @ [Suc i]" "[3 ..< Suc (Suc i)] = [3 ..< Suc i] @ [Suc i]" by auto
  have cong: "\<And> a b c d. a = c \<Longrightarrow> b = d \<Longrightarrow> a * b = c * (d :: 'a fract)" by auto
  define AB where "AB = (\<lambda> l. \<beta> l / \<alpha> l)"
  define ABP where "ABP = (\<lambda> l. AB l ^ (n (l - 1) - n i) * f (l - 1) ^ (\<delta> (l - 2) + \<delta> (l - 1)))"
  define PR where "PR = (\<Prod>l\<leftarrow>[3..<Suc i]. ABP l)"
  define PR2 where "PR2 = (\<Prod>l\<leftarrow>[3..<Suc i]. AB l)"
  from F0[of i]
  have "\<Theta> i * f i / \<gamma> (i + 1) = (
  ((- 1) ^ \<tau> i * (- 1) ^ \<sigma> (i + 1)) * (pow_int (f i) (int (\<delta> (i - 1)) - 1) *
    PR * f i /
    pow_int (f i) (1 - int (\<delta> i)) / ((\<Prod>l\<leftarrow>[3..<Suc i]. ABP l * AB l) *
        AB (Suc i) * f i ^ (\<delta> (i - 1) + \<delta> i))))"
    unfolding id prod_list.append map_append \<Theta>_def \<gamma>_def divide_prod_assoc
    by (simp add: field_simps power_add AB_def ABP_def PR_def)
  also have "(- 1 :: 'a fract) ^ \<tau> i * (- 1) ^ \<sigma> (i + 1) = (- 1) ^ (\<tau> i + \<sigma> (i + 1))"
    unfolding power_add by (auto simp: field_simps)
  also have "\<dots> = (- 1) ^ (n 1 + n i + i + 1)"
  proof (cases "i = 2")
    case True
    show ?thesis unfolding \<tau>_def \<sigma>_def True by (auto, rule minus_1_even_eqI, auto)
  next
    case False
    define a where "a = (\<lambda> l. n (l - 2) + n i)"
    define b where "b = (\<lambda> l. n (l - 1) + n i)"
    define c where "c = (\<Sum>l\<leftarrow>[3..<Suc i]. (a l * b l + n i))"
    define d where "d = c + (\<Sum>l\<leftarrow>[3..<i]. n (l - 1))"
    define e where "e = (n (i - 1) + n i + 1) * n i"
    have "(\<tau> i + \<sigma> (i + 1)) =
      ((\<Sum>l\<leftarrow>[3..<Suc i]. (a l * b l) + (a l + 1) * (b l + 1))) + (a (Suc i) + 1) * (b (Suc i) + 1)"
      unfolding \<sigma>_def \<tau>_def id a_def b_def sum_list_addf by simp
    also have "(\<Sum>l\<leftarrow>[3..<Suc i]. (a l * b l) + (a l + 1) * (b l + 1)) =
       (\<Sum>l\<leftarrow>[3..<Suc i]. 2 * a l * b l + (a l + b l) + 1)"
      by (rule arg_cong, rule map_cong, auto)
    also have "\<dots> = (\<Sum>l\<leftarrow>[3..<Suc i]. 2 * (a l * b l + n i) + (n (l - 1) + n (l - 2)) + 1)"
      by (simp add: field_simps a_def b_def)
    also have "\<dots> = 2 * c + (\<Sum>l\<leftarrow>[3..<Suc i]. (n (l - 1) + n (l - 2))) + length [3 ..< Suc i]"
      unfolding sum_list_addf c_def sum_list_const_mult sum_list_triv by simp
    also have "(\<Sum>l\<leftarrow>[3..<Suc i]. (n (l - 1) + n (l - 2)))
      = (\<Sum>l\<leftarrow>[3..<Suc i]. n (l - 1)) + (\<Sum>l\<leftarrow>[3..<Suc i]. n (l - 2))"
      by (simp add: sum_list_addf)
    also have "(\<Sum>l\<leftarrow>[3..<Suc i]. n (l - 2)) = (\<Sum>l\<leftarrow>3 # [4..<Suc i]. n (l - 2))"
      by (rule arg_cong, rule map_cong, insert i False, auto simp: upt_rec[of 3])
    also have "\<dots> = n 1 + (\<Sum>l\<leftarrow>[(Suc 3)..<Suc i]. n (l - 2))" by auto
    also have "(\<Sum>l\<leftarrow>[(Suc 3)..<Suc i]. n (l - 2)) = (\<Sum>l\<leftarrow>[3..<i]. n (l - 1))"
    proof (rule arg_cong[of _ _ sum_list], rule nth_equalityI, force, auto simp: nth_append, goal_cases)
      case (1 j)
      hence "i - 2 = Suc (Suc j)" by simp
      thus ?case by simp
    qed
    also have "(\<Sum>l\<leftarrow>[3..<Suc i]. n (l - 1)) = (\<Sum>l\<leftarrow>[3..<i] @ [i]. n (l - 1))"
      by (rule arg_cong, rule map_cong, insert i False, auto)
    finally have "\<tau> i + \<sigma> (i + 1) =
      2 * d + n (i - 1) + n 1 +  length [3..<Suc i] + (a (Suc i) + 1) * (b (Suc i) + 1)"
      by (simp add: d_def)
    also have "length [3 ..< Suc i] = i - 2" using i by auto
    also have "(a (Suc i) + 1) * (b (Suc i) + 1) = 2 * e + n (i - 1) + n i + 1" unfolding a_def b_def e_def
      by simp
    finally have id: "\<tau> i + \<sigma> (i + 1) = 2 * (d + n (i - 1) + e) + n 1 + (i - 2) + n i + 1"
      by simp
    show ?thesis
      by (rule minus_1_even_eqI, unfold id, insert i, auto)
  qed
  also have "(\<Prod>l\<leftarrow>[3..<Suc i]. ABP l * AB l) = PR * PR2"
    unfolding PR_def prod_list_multf PR2_def by simp
  also have "(pow_int (f i) (int (\<delta> (i - 1)) - 1) * PR * f i / pow_int (f i) (1 - int (\<delta> i))
    / (PR * PR2 * AB (Suc i) * f i ^ (\<delta> (i - 1) + \<delta> i))) =
    ((pow_int (f i) (int (\<delta> (i - 1)) - 1) * pow_int (f i) 1 * pow_int (f i) (int (\<delta> i) - 1)
    / pow_int (f i) (int (\<delta> (i - 1) + \<delta> i)))) * (PR / PR / (PR2 * AB (Suc i)))"
    (is "\<dots> = ?x * ?y")
    unfolding exp_pow_int[symmetric] by (simp add: pow_int_divide ac_simps)
  also have "?x = pow_int (f i) (-1)"
    unfolding pow_int_divide pow_int_add[OF ff0, symmetric] by simp
  also have "\<dots> = 1 / (f i)"
    unfolding pow_int_def by simp
  also have "PR / PR = 1"
  proof -
    have "PR \<noteq> 0" unfolding PR_def prod_list_zero_iff set_map
    proof
      assume "0 \<in> ABP ` set [3 ..< Suc i]"
      then obtain j where j: "3 \<le> j" "j < Suc i" and 0: "ABP j = 0" by auto
      with i have jk: "j \<le> k" and j1: "j - 1 \<noteq> 0" "j - 1 < k" by auto
      hence 1: "\<alpha> j \<noteq> 0" "f (j - 1) \<noteq> 0" using \<alpha>0 f0 by auto
      with 0 have "AB j = 0" unfolding ABP_def by simp
      from this[unfolded AB_def] 1(1) \<beta>0[of j] show False by auto
    qed
    thus ?thesis by simp
  qed
  also have "PR2 * AB (Suc i) = (\<Prod>l\<leftarrow>[3..<Suc (Suc i)]. AB l)" unfolding id PR2_def by auto
  also have "1 / \<dots> = inverse \<dots>" by (simp add: inverse_eq_divide)
  also have "\<dots> = (\<Prod>l\<leftarrow>[3..<Suc (Suc i)]. \<alpha> l / \<beta> l)" unfolding AB_def
    inverse_prod_list map_map o_def
    by (auto cong: map_cong)
  finally show ?thesis by simp
qed

lemma B_theorem_3: "h i = \<Theta> i * f i" "h i = ff (lead_coeff (H i))"
proof -
  have "\<Theta> i * f i = \<Theta> i * f i / \<gamma> (i + 1)"
    using B_theorem_2[of "i + 1"] i by auto
  also have "\<dots> = (- 1) ^ (n 1 + n i + i + 1) / f i *
    (\<Prod>l\<leftarrow>[3..<Suc (Suc i)]. \<alpha> l / \<beta> l)" by (rule B_theorem_3_main)
  also have "\<dots> = h i" using B_eq_17[of i] i by simp
  finally show "h i = \<Theta> i * f i" ..
  thus "h i = ff (lead_coeff (H i))" using B_theorem_3_b by auto
qed
end

lemma h0: "i \<le> k \<Longrightarrow> h i \<noteq> 0"
proof (induct i)
  case (Suc i)
  thus ?case unfolding h.simps[of "Suc i"] using f0 by (auto simp del: h.simps)
qed auto

lemma deg_G12: "degree G1 \<ge> degree G2" using n12
  unfolding n F1 F2 by auto

lemma R0: shows "R 0 = [: resultant G1 G2 :]"
proof(cases "n 2 = 0")
  case True
  hence d:"degree G2 = 0" unfolding n F2 by auto
  from degree0_coeffs[OF d] F2 F12 obtain a where
    G2: "G2 = [:a:]" and a: "a \<noteq> 0" by auto
  have "sdiv_poly [:a * a ^ degree G1:] a = [:a ^ degree G1:]" using a
    unfolding sdiv_poly_def by auto
  note dp = this
  show ?thesis using G2 F12
    unfolding R_def \<delta> n F1 F2 Suc_1 by (auto split:if_splits simp:mult.commute dp)
next
  case False
  from False n12 have d:"degree G2 \<noteq> 0" "degree G2 \<le> degree G1" unfolding n F2 F1 by auto
  from False have "R 0 = subresultant 0 G1 G2" unfolding R_def by simp
  also have "\<dots> = [: resultant G1 G2 :]" unfolding subresultant_resultant by simp
  finally show ?thesis .
qed

context
  fixes div_exp :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  assumes div_exp: "\<And> x y n.
     (to_fract x)^n / (to_fract y)^(n-1) \<in> range to_fract
     \<Longrightarrow> to_fract (div_exp x y n) = (to_fract x)^n / (to_fract y)^(n-1)"
begin
lemma subresultant_prs_main: assumes "subresultant_prs_main div_exp Gi_1 Gi hi_1 = (Gk, hk)"
  and "F i = ffp Gi"
  and "F (i - 1) = ffp Gi_1"
  and "h (i - 1) = ff hi_1"
  and "i \<ge> 3" "i \<le> k"
shows "F k = ffp Gk \<and> h k = ff hk \<and> (\<forall> j. i \<le> j \<longrightarrow> j \<le> k \<longrightarrow> F j \<in> range ffp \<and> \<beta> (Suc j) \<in> range ff)"
proof -
  obtain m where m: "m = k - i" by auto
  show ?thesis using m assms
  proof (induct m arbitrary: Gi_1 Gi hi_1 i rule: less_induct)
    case (less m Gi_1 Gi hi_1 i)
    note IH = less(1)
    note m = less(2)
    note res = less(3)
    note id = less(4-6)
    note i = less(7-8)
    let ?pmod = "pseudo_mod Gi_1 Gi"
    let ?ni = "degree Gi"
    let ?ni_1 = "degree Gi_1"
    let ?gi = "lead_coeff Gi"
    let ?gi_1 = "lead_coeff Gi_1"
    let ?d1 = "?ni_1 - ?ni"
    obtain hi where hi: "hi = div_exp ?gi hi_1 ?d1" by auto
    obtain divisor where div: "divisor = (-1) ^ (?d1 + 1) * ?gi_1 * (hi_1 ^ ?d1)" by auto
    obtain G1_p1 where G1_p1: "G1_p1 = sdiv_poly ?pmod divisor" by auto
    note res = res[unfolded subresultant_prs_main.simps[of div_exp Gi_1] Let_def,
      folded hi, folded div, folded G1_p1]
    have h_i: "h i = f i ^ \<delta> (i - 1) / h (i - 1) ^ (\<delta> (i - 1) - 1)" unfolding h.simps[of i] using i by simp
    have hi_ff: "h i \<in> range ff" using B_theorem_3[OF _ i(2)] i by auto
    have d1: "\<delta> (i - 1) = ?d1" unfolding \<delta> n using id(1,2) using i by simp
    have fi: "f i = ff ?gi" unfolding f id by simp
    have fi1: "f (i - 1) = ff ?gi_1" unfolding f id by simp
    have eq': "h i = ff (lead_coeff Gi) ^ \<delta> (i - 1) / ff hi_1 ^ (\<delta> (i - 1) - 1)"
      unfolding h_i fi id ..
    have idh: "h i = ff hi" using hi_ff h_i fi id
      unfolding hi d1[symmetric]
      by (subst div_exp[of ?gi "\<delta> (i - 1)" hi_1], unfold eq'[symmetric], insert assms, blast+)
    have "\<beta> (Suc i) = (- 1) ^ (\<delta> (i - 1) + 1) * f (i - 1) * h (i - 1) ^ \<delta> (i - 1)"
      using \<beta>i[of "Suc i"] i by auto
    also have "\<dots> = ff ((- 1) ^ (\<delta> (i - 1) + 1) * lead_coeff Gi_1 * hi_1 ^ \<delta> (i - 1))"
      unfolding id f by (simp add: hom_distribs)
    also have "\<dots> \<in> range ff" by blast
    finally have beta: "\<beta> (Suc i) \<in> range ff" .
    have pm: "pseudo_mod (F (i - 1)) (F i) = ffp ?pmod"
      unfolding to_fract_hom.pseudo_mod_hom[symmetric] id by simp
    have eq: "(?pmod = 0) = (i = k)"
      using pm i pmod[of "Suc i"] F0[of "Suc i"] i \<beta>0[of "Suc i"] by auto
    show ?case
    proof (cases "i = k")
      case True
      with res eq have res: "Gk = Gi" "hk = hi" by auto
      with pmod
      have "F k = ffp Gk \<and> h k = ff hk" unfolding res idh[symmetric] id[symmetric] True by auto
      thus ?thesis using beta unfolding True by auto
    next
      case False
      with res eq have res:
         "subresultant_prs_main div_exp Gi G1_p1 hi = (Gk, hk)" by auto
      from m False i have m: "m - 1 < m" "m - 1 = k - Suc i" by auto
      have si: "Suc i - 1 = i" and ii: "3 \<le> Suc i" "Suc i \<le> k" and iii: "3 \<le> Suc i" "Suc i \<le> Suc k"
        using False i by auto
      have *: "(\<forall>j\<ge>Suc i. j \<le> k \<longrightarrow> F j \<in> range ffp \<and> \<beta> (Suc j) \<in> range ff) = (\<forall>j\<ge>i. j \<le> k \<longrightarrow> F j \<in> range ffp  \<and> \<beta> (Suc j) \<in> range ff)"
        by (rule for_all_Suc, insert id(1) beta, auto)
      show ?thesis
      proof (rule IH[OF m res, unfolded si, OF _ id(1) idh ii, unfolded *])
        have F_ffp: "F (Suc i) \<in> range ffp" using fundamental_theorem_eq_4[OF ii, symmetric] B_theorem_2[OF iii] by auto
        from pmod[OF iii] have "smult (\<beta> (Suc i)) (F (Suc i)) = pseudo_mod (F (i - 1)) (F i)"
          by simp
        from arg_cong[OF this, of "\<lambda> x. smult (inverse (\<beta> (Suc i))) x"]
        have Fsi: "F (Suc i) = smult (inverse (\<beta> (Suc i))) (pseudo_mod (F (i - 1)) (F i))"
          using \<beta>0[of "Suc i"] by auto
        show "F (Suc i) = ffp G1_p1"
        proof (rule smult_inverse_sdiv_poly[OF F_ffp Fsi G1_p1 _ pm])
          from i ii have iv: "4 \<le> Suc i" "Suc i \<le> Suc k" by auto
          have *: "Suc i - 2 = i - 1" by auto
          show "\<beta> (Suc i) = ff divisor" unfolding \<beta>i[OF iv] div d1 * fi1
            using id by (simp add: hom_distribs)
        qed
      qed
    qed
  qed
qed

lemma subresultant_prs: assumes res: "subresultant_prs div_exp G1 G2 = (Gk, hk)"
  shows "F k = ffp Gk \<and> h k = ff hk \<and> (i \<noteq> 0 \<longrightarrow> F i \<in> range ffp) \<and> (3 \<le> i \<longrightarrow> i \<le> Suc k \<longrightarrow> \<beta> i \<in> range ff)"
proof -
  let ?pmod = "pseudo_mod G1 G2"
  have pm: "pseudo_mod (F 1) (F 2) = ffp ?pmod"
    unfolding to_fract_hom.pseudo_mod_hom[symmetric] F1 F2 by simp
  let ?g2 = "lead_coeff G2"
  let ?n2 = "degree G2"
  obtain d1 where d1: "d1 = degree G1 - ?n2" by auto
  obtain h2 where h2: "h2 = ?g2 ^ d1" by auto
  have "(?pmod = 0) = (pseudo_mod (F 1) (F 2) = 0)" using pm by auto
  also have "\<dots> = (k < 3)" using k2 pmod[of 3] F0[of 3] \<beta>0[of 3] by auto
  finally have eq: "?pmod = 0 \<longleftrightarrow> k = 2" using k2 by linarith
  note res = res[unfolded subresultant_prs_def Let_def eq, folded d1, folded h2]
  have idh2: "h 2 = ff h2" unfolding h2 d1 h.simps[of 2] \<delta> n F1
    using F2 by (simp add: numeral_2_eq_2 f hom_distribs)
  have main: "F k = ffp Gk \<and> h k = ff hk \<and> (i \<ge> 3 \<longrightarrow> i \<le> k \<longrightarrow> F i \<in> range ffp \<and> \<beta> (Suc i) \<in> range ff)" for i
  proof (cases "k = 2")
    case True
    with res have "Gk = G2" "hk = h2" by auto
    thus ?thesis using True idh2 F2 by auto
  next
    case False
    hence "(k = 2) = False" by simp
    note res = res[unfolded this if_False]
    have F_2: "F (3 - 1) = ffp G2" using F2 by simp
    have h2: "h (3 - 1) = ff h2" using idh2 by simp
    have n2: "degree G2 = n (3 - 1)" unfolding n using F2 by simp
    from False k2 have k3: "3 \<le> k" by auto
    have "F k = ffp Gk \<and> h k = ff hk \<and> (\<forall>j\<ge>3. j \<le> k \<longrightarrow> F j \<in> range ffp \<and> \<beta> (Suc j) \<in> range ff)"
    proof (rule subresultant_prs_main[OF res _ F_2 h2 le_refl k3])
      let ?pow = "(- 1) ^ (\<delta> 1 + 1) :: 'a fract"
      from pmod[of 3] k3
      have "smult (\<beta> 3) (F 3) = pseudo_mod (F 1) (F 2)" by simp
      also have "\<dots> = pseudo_mod (ffp G1) (ffp G2)" using F1 F2 by auto
      also have "\<dots> = ffp (pseudo_mod G1 G2)" unfolding to_fract_hom.pseudo_mod_hom by simp
      also have "\<beta> 3 = (- 1) ^ (\<delta> 1 + 1)" unfolding \<beta>3 by simp
      finally have "smult ((- 1) ^ (\<delta> 1 + 1)) (F 3) = ffp (pseudo_mod G1 G2)" by simp
      also have "smult ((- 1) ^ (\<delta> 1 + 1)) (F 3) = [: ?pow :] * F 3"
        by simp
      also have "[: ?pow :] = (- 1) ^ (\<delta> 1 + 1)" by (unfold hom_distribs, simp)
      finally have "(- 1) ^ (\<delta> 1 + 1) * F 3 = ffp (pseudo_mod G1 G2)" by simp
      from arg_cong[OF this, of "\<lambda> i. (- 1) ^ (\<delta> 1 + 1) * i"]
      have "F 3 = (- 1) ^ (\<delta> 1 + 1) * ffp (pseudo_mod G1 G2)" by simp
      also have "\<delta> 1 = d1" unfolding \<delta> n d1 using F1 F2 by (simp add: numeral_2_eq_2)
      finally show F3: "F 3 = ffp ((- 1) ^ (d1 + 1) * pseudo_mod G1 G2)" by (simp add: hom_distribs)
    qed
    thus ?thesis by auto
  qed
  show ?thesis
  proof (intro conjI impI)
    assume "i \<noteq> 0"
    then consider (12) "i = 1 \<or> i = 2" | (i3) "i \<ge> 3 \<and> i \<le> k" | (ik) "i > k" by linarith
    thus "F i \<in> range ffp"
    proof cases
      case 12
      thus ?thesis using F1 F2 by auto
    next
      case i3
      thus ?thesis using main by auto
    next
      case ik
      hence "F i = 0" using F0 by auto
      thus ?thesis by simp
    qed
  next
    assume "3 \<le> i" and "i \<le> Suc k"
    then consider (3) "i = 3" | (4) "3 \<le> i - 1" "i - 1 \<le> k" by linarith
    thus "\<beta> i \<in> range ff"
    proof (cases)
      case 3
      have "\<beta> i = ff ((- 1) ^ (\<delta> 1 + 1))" unfolding 3 \<beta>3 by (auto simp: hom_distribs)
      thus ?thesis by blast
    next
      case 4
      with main[of "i - 1"] show ?thesis by auto
    qed
  qed (insert main, auto)
qed

lemma resultant_impl_main: "resultant_impl_main div_exp G1 G2 = resultant G1 G2"
proof -
  from F0[of 2] F12(2) have k2: "k \<ge> 2" by auto
  obtain Gk hk where sub: "subresultant_prs div_exp G1 G2 = (Gk, hk)" by force
  from subresultant_prs[OF this] have *: "F k = ffp Gk" "h k = ff hk" by auto
  have "resultant_impl_main div_exp G1 G2 = (if degree (F k) = 0 then hk else 0)"
    unfolding resultant_impl_main_def sub split * using F2 F12 by auto
  also have "\<dots> = resultant G1 G2"
  proof (cases "n k = 0")
    case False
    with fundamental_theorem_eq_7[of 0] show ?thesis unfolding n[of k] * R0 by auto
  next
    case True
    from H_def[of k, unfolded True] have R: "R 0 = H k" by simp
    show ?thesis
    proof (cases "k = 2")
      case False
      with k2 have k3: "k \<ge> 3" by auto
      from B_theorem_3[OF k3] R0 R have "h k = ff (resultant G1 G2)" by simp
      from this[folded *] * have "hk = resultant G1 G2" by simp
      with True show ?thesis unfolding n by auto
    next
      case 2: True
      have id: "(if degree (F k) = 0 then hk else 0) = hk" using True unfolding n by simp
      from F0[of 3, unfolded 2] have "F 3 = 0" by simp
      with pmod[of 3, unfolded 2] \<beta>0[of 3] have "pseudo_mod (F 1) (F 2) = 0" by auto
      hence pm: "pseudo_mod G1 G2 = 0" unfolding F1 F2 to_fract_hom.pseudo_mod_hom by simp
      from subresultant_prs_def[of div_exp G1 G2, unfolded sub Let_def this]
      have id: "Gk = G2" "hk = lead_coeff G2 ^ (degree G1 - degree G2)" by auto
      from F12 F1 F2 have "G1 \<noteq> 0" "G2 \<noteq> 0" by auto
      from resultant_pseudo_mod_0[OF pm deg_G12 this]
      have res: "resultant G1 G2 = (if degree G2 = 0 then lead_coeff G2 ^ degree G1 else 0)"
        by simp
      from True[unfolded 2 n F2] have "degree G2 = 0" by simp
      thus ?thesis unfolding res 2 F2 id by simp
    qed
  qed
  finally show ?thesis .
qed
end
end

text \<open>At this point, we have soundness of the resultant-implementation, provided that we can
  instantiate the locale by constructing suitable values of F, b, h, etc. Now we show the
  existence of suitable locale parameters by constructively computing them.\<close>

context
  fixes G1 G2 :: "'a :: idom_divide poly"
begin

private function F and b and h where "F i = (if i = (0 :: nat) then 1
  else if i = 1 then map_poly to_fract G1 else if i = 2 then map_poly to_fract G2
  else (let G = pseudo_mod (F (i - 2)) (F (i - 1))
    in if F (i - 1) = 0 \<or> G = 0 then 0 else smult (inverse (b i)) G))"
| "b i = (if i \<le> 2 then 1 else
   if i = 3 then (- 1) ^ (degree (F 1) - degree (F 2) + 1)
   else if F (i - 2) = 0 then 1 else (- 1) ^ (degree (F (i - 2)) - degree (F (i - 1)) + 1) * lead_coeff (F (i - 2)) *
         h (i - 2) ^ (degree (F (i - 2)) - degree (F (i - 1))))"
| "h i = (if (i \<le> 1) then 1 else if i = 2 then (lead_coeff (F 2) ^ (degree (F 1) - degree (F 2))) else
    if F i = 0 then 1 else (lead_coeff (F i) ^ (degree (F (i - 1)) - degree (F i)) / (h (i - 1) ^ ((degree (F (i - 1)) - degree (F i)) - 1))))"
  by pat_completeness auto
termination
proof
  show "wf (measure (case_sum (\<lambda> fi. 3 * fi +1)  (case_sum (\<lambda> bi. 3 * bi) (\<lambda> hi. 3 * hi + 2))))" by simp
qed (auto simp: termination_simp)

declare h.simps[simp del] b.simps[simp del] F.simps[simp del]

private lemma Fb0: assumes base: "G1 \<noteq> 0" "G2 \<noteq> 0"
  shows "(F i = 0 \<longrightarrow> F (Suc i) = 0) \<and> b i \<noteq> 0 \<and> h i \<noteq> 0"
proof (induct i rule: less_induct)
  case (less i)
  note * [simp] = F.simps[of i] b.simps[of i] h.simps[of i]
  consider (0) "i = 0" | (1) "i = 1" | (2) "i \<ge> 2" by linarith
  thus ?case
  proof cases
    case 0
    show ?thesis unfolding * unfolding 0 by simp
  next
    case 1
    show ?thesis unfolding * unfolding 1 using assms by simp
  next
    case 2
    have F: "F i = 0 \<Longrightarrow> F (Suc i) = 0" unfolding F.simps[of "Suc i"] using 2 by simp
    from assms have F2: "F 2 \<noteq> 0" unfolding F.simps[of 2] by simp
    from 2 have "i - 1 < i" "i - 2 < i" by auto
    note IH = less[OF this(1)] less[OF this(2)]
    hence b: "b (i - 1) \<noteq> 0" and h: "h (i - 1) \<noteq> 0" "h (i - 2) \<noteq> 0" by auto
    from h have hi: "h i \<noteq> 0" unfolding h.simps[of i] using 2 F2 by auto
    have bi: "b i \<noteq> 0" unfolding b.simps[of i] using h(2) by auto
    show ?thesis using hi bi F by blast
  qed
qed

private definition "k = (LEAST i. F (Suc i) = 0)"

private lemma k_exists: "\<exists> i. F (Suc i) = 0"
proof -
  obtain n i where "i \<ge> 3" "length (coeffs (F (Suc i))) = n" by blast
  thus ?thesis
  proof (induct n arbitrary: i rule: less_induct)
    case (less n i)
    let ?ii = "Suc (Suc i)"
    let ?i = "Suc i"
    from less(2) have i: "?i \<ge> 3" by auto
    let ?mod = "pseudo_mod (F (?ii - 2)) (F ?i)"
    have Fi: "F ?ii = (if F ?i = 0 \<or> ?mod = 0 then 0 else smult (inverse (b ?ii)) ?mod)"
      unfolding F.simps[of ?ii] using i by auto
    show ?case
    proof (cases "F ?ii = 0")
      case False
      hence Fi: "F ?ii = smult (inverse (b ?ii)) ?mod" and mod: "?mod \<noteq> 0" and Fi1: "F ?i \<noteq> 0"
        unfolding Fi by auto
      from pseudo_mod[OF Fi1, of "F (?ii - 2)"] mod have "degree ?mod < degree (F ?i)" by simp
      hence deg: "degree (F ?ii) < degree (F ?i)" unfolding Fi by auto
      hence "length (coeffs (F ?ii)) < length (coeffs (F ?i))" unfolding degree_eq_length_coeffs by auto
      from less(1)[OF _ i refl, folded less(3), OF this] show ?thesis by auto
    qed blast
  qed
qed

private lemma k: "F (Suc k) = 0" "i < k \<Longrightarrow> F (Suc i) \<noteq> 0"
proof -
  show "F (Suc k) = 0" unfolding k_def using k_exists by (rule LeastI2_ex)
  assume "i < k" from not_less_Least[OF this[unfolded k_def]] show "F (Suc i) \<noteq> 0" .
qed

lemma enter_subresultant_prs: assumes len: "length (coeffs G1) \<ge> length (coeffs G2)"
  and G2: "G2 \<noteq> 0"
shows "\<exists> F n d f k b. subresultant_prs_locale2 F n d f k b G1 G2"
proof (intro exI)
  from G2 len have G1: "G1 \<noteq> 0" by auto
  from len have deg_le: "degree (F 2) \<le> degree (F 1)"
    by (simp add: F.simps degree_eq_length_coeffs)
  from G2 G1 have F1: "F 1 \<noteq> 0" and F2: "F 2 \<noteq> 0" by (auto simp: F.simps)
  note Fb0 = Fb0[OF G1 G2]
  interpret s: subresultant_prs_locale F "\<lambda> i. degree (F i)" "\<lambda> i. degree (F i) - degree (F (Suc i))"
    "\<lambda> i. lead_coeff (F i)" k b G1 G2
  proof (unfold_locales, rule refl, rule refl, rule refl, rule deg_le, rule F1, rule F2)
    from k(1) F1 have k0: "k \<noteq> 0" by (cases k, auto)
    show Fk: "(F i = 0) = (k < i)" for i
    proof
      assume "F i = 0" with k(2)[of "i - 1"]
      have "\<not> (i - 1 < k)" by (cases i, auto simp: F.simps)
      thus "i > k" using k0 by auto
    next
      assume "i > k"
      then obtain j l where i: "i = j + l" and "j = Suc k" and "l = i - Suc k" and Fj: "F j = 0" using k(1)
        by auto
      with F1 F2 k0 have j2: "j \<ge> 2" by auto
      show "F i = 0" unfolding i
      proof (induct l)
        case (Suc l)
        thus ?case unfolding F.simps[of "j + Suc l"] using j2 by auto
      qed (auto simp: Fj)
    qed
    show b: "b i \<noteq> 0" for i using Fb0 by blast
    show "F 1 = map_poly to_fract G1" unfolding F.simps[of 1] by simp
    show "F 2 = map_poly to_fract G2" unfolding F.simps[of 2] by simp
    fix i
    let ?mod = "pseudo_mod (F (i - 2)) (F (i - 1))"
    assume i: "3 \<le> i" "i \<le> Suc k"
    from Fk[of "i - 1"] i have "F (i - 1) \<noteq> 0" by auto
    with i have Fi: "F i = (if ?mod = 0 then 0 else smult (inverse (b i)) ?mod)" unfolding F.simps[of i]
      Let_def by simp
    show "smult (b i) (F i) = ?mod"
    proof (cases "?mod = 0")
      case True
      thus ?thesis unfolding Fi by simp
    next
      case False
      with Fi have Fi: "F i = smult (inverse (b i)) ?mod" by simp
      from arg_cong[OF this, of "smult (b i)"] b[of i] show ?thesis by simp
    qed
  qed
  note s.h.simps[simp del]
  show "subresultant_prs_locale2 F (\<lambda> i. degree (F i)) (\<lambda> i. degree (F i) - degree (F (Suc i)))
    (\<lambda> i. lead_coeff (F i)) k b G1 G2"
  proof
    show "b 3 = (- 1) ^ (degree (F 1) - degree (F (Suc 1)) + 1)" unfolding b.simps numeral_2_eq_2 by simp
    fix i
    assume i: "4 \<le> i" "i \<le> Suc k"
    with s.F0[of "i - 2"] have "F (i - 2) \<noteq> 0" by auto
    hence bi: "b i = (- 1) ^ (degree (F (i - 2)) - degree (F (i - 1)) + 1) * lead_coeff (F (i - 2)) *
                    h (i - 2) ^ (degree (F (i - 2)) - degree (F (i - 1)))" unfolding b.simps
      using i by auto
    have "i < k \<Longrightarrow> s.h i = h i" for i
    proof (induct i)
      case 0
      thus ?case by (simp add: h.simps s.h.simps)
    next
      case (Suc i)
      from Suc(2) s.F0[of "Suc i"] have "F (Suc i) \<noteq> 0" by auto
      with Suc show ?case unfolding h.simps[of "Suc i"] s.h.simps[of "Suc i"] numeral_2_eq_2 by simp
    qed
    hence sh: "s.h (i - 2) = h (i - 2)" using i by simp
    from i have *: "Suc (i - 2) = i - 1" by auto
    show "b i = (- 1) ^ (degree (F (i - 2)) - degree (F (Suc (i - 2))) + 1) * lead_coeff (F (i - 2)) *
         s.h (i - 2) ^ (degree (F (i - 2)) - degree (F (Suc (i - 2))))"
      unfolding sh bi * ..
  qed
qed
end

text \<open>Now we obtain the soundness lemma outside the locale.\<close>

context
  fixes div_exp :: "'a :: idom_divide \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  assumes div_exp: "\<And> x y n.
     (to_fract x)^n / (to_fract y)^(n-1) \<in> range to_fract
     \<Longrightarrow> to_fract (div_exp x y n) = (to_fract x)^n / (to_fract y)^(n-1)"
begin

lemma resultant_impl_main: assumes len: "length (coeffs G1) \<ge> length (coeffs G2)"
  shows "resultant_impl_main div_exp G1 G2 = resultant G1 G2"
proof (cases "G2 = 0")
  case G2: False
  from enter_subresultant_prs[OF len G2] obtain F n d f k b
    where "subresultant_prs_locale2 F n d f k b G1 G2" by auto
  interpret subresultant_prs_locale2 F n d f k b G1 G2 by fact
  show ?thesis by (rule resultant_impl_main[OF div_exp])
next
  case G2: True
  show ?thesis unfolding G2
    resultant_impl_main_def using resultant_const(2)[of G1 0] by simp
qed

theorem resultant_impl_generic: "resultant_impl_generic div_exp = resultant"
proof (intro ext)
  fix f g :: "'a poly"
  show "resultant_impl_generic div_exp f g = resultant f g"
  proof (cases "length (coeffs f) \<ge> length (coeffs g)")
    case True
    thus ?thesis unfolding resultant_impl_generic_def resultant_impl_main[OF True] by auto
  next
    case False
    hence "length (coeffs g) \<ge> length (coeffs f)" by auto
    from resultant_impl_main[OF this]
    show ?thesis unfolding resultant_impl_generic_def resultant_swap[of f g] using False
      by (auto simp: Let_def)
  qed
qed
end

lemma resultant_impl[simp]: "resultant_impl = resultant"
  unfolding resultant_impl_def
  by (rule resultant_impl_generic[OF dichotomous_Lazard])

lemma resultant_impl_idom_divide[simp]: "resultant_impl_idom_divide = resultant"
  unfolding resultant_impl_idom_divide_def
  by (rule resultant_impl_generic[OF basic_div_exp])

subsection \<open>Code Equations\<close>

text \<open>In the following code-equations, we only compute the required values, e.g., $h_k$
  is not required if $n_k > 0$, we compute $(-1)^{\ldots} * \ldots$ via a case-analysis,
  and we perform special cases for $\delta_i = 1$, which is the most frequent case.\<close>

partial_function(tailrec) subresultant_prs_main_impl where
  "subresultant_prs_main_impl f Gi_1 Gi ni_1 d1_1 hi_2 = (let
     gi_1 = lead_coeff Gi_1;
     ni = degree Gi;
     hi_1 = (if d1_1 = 1 then gi_1 else dichotomous_Lazard gi_1 hi_2 d1_1);
     d1 = ni_1 - ni;
     pmod = pseudo_mod Gi_1 Gi
    in (if pmod = 0 then f (Gi, (if d1 = 1 then lead_coeff Gi
      else dichotomous_Lazard (lead_coeff Gi) hi_1 d1)) else
    let
       gi = lead_coeff Gi;
       divisor = (-1) ^ (d1 + 1) * gi_1 * (hi_1 ^ d1) ;
       Gi_p1 = sdiv_poly pmod divisor
       in subresultant_prs_main_impl f Gi Gi_p1 ni d1 hi_1))"

definition subresultant_prs_impl where
  [code del]: "subresultant_prs_impl f G1 G2 = (let
    pmod = pseudo_mod G1 G2;
    n2 = degree G2;
    delta_1 = (degree G1 - n2);
    g2 = lead_coeff G2;
    h2 = g2 ^ delta_1
    in if pmod = 0 then f (G2,h2) else let
      G3 = (- 1) ^ (delta_1 + 1) * pmod;
      g3 = lead_coeff G3;
      n3 = degree G3;
      d2 = n2 - n3;
      pmod = pseudo_mod G2 G3
    in if pmod = 0 then f (G3, if d2 = 1 then g3 else dichotomous_Lazard g3 h2 d2)
    else let divisor = (- 1) ^ (d2 + 1) * g2 * h2 ^ d2; G4 = sdiv_poly pmod divisor
         in subresultant_prs_main_impl f G3 G4 n3 d2 h2
    )"

lemma subresultant_prs_impl: "subresultant_prs_impl f G1 G2 = f (subresultant_prs dichotomous_Lazard G1 G2)"
proof -
  define h2 where "h2 = lead_coeff G2 ^ (degree G1 - degree G2)"
  define G3 where "G3 = ((- 1) ^ (degree G1 - degree G2 + 1) * pseudo_mod G1 G2)"
  define G4 where "G4 = sdiv_poly (pseudo_mod G2 G3)
       ((- 1) ^ (degree G2 - degree G3 + 1) * lead_coeff G2 *
        h2 ^ (degree G2 - degree G3))"
  define d2 where "d2 = degree G2 - degree G3"
  have dl1: "(if d = 1 then (g :: 'b) else dichotomous_Lazard g h d) = dichotomous_Lazard g h d" for d g h
    by (cases "d = 1", auto simp: dichotomous_Lazard dichotomous_Lazard.simps)
  show ?thesis
    unfolding subresultant_prs_impl_def subresultant_prs_def Let_def
      subresultant_prs_main.simps[of dichotomous_Lazard G2]
      if_distrib[of f] dl1
  proof (rule if_cong[OF refl refl if_cong[OF refl refl]], unfold h2_def[symmetric],
    unfold G3_def[symmetric], unfold G4_def[symmetric], unfold d2_def[symmetric])
    note simp = subresultant_prs_main_impl.simps[of f] subresultant_prs_main.simps[of dichotomous_Lazard]
    show "subresultant_prs_main_impl f G3 G4 (degree G3) d2 h2 =
      f (subresultant_prs_main dichotomous_Lazard G3 G4 (dichotomous_Lazard (lead_coeff G3) h2 d2))"
    proof (induct G4 arbitrary: G3 d2 h2 rule: wf_induct[OF wf_measure[of degree]])
      case (1 G4 G3 d2 h2)
      let ?M = "pseudo_mod G3 G4"
      show ?case
      proof (cases "?M = 0")
        case True
        thus ?thesis unfolding simp[of G3] Let_def dl1 by simp
      next
        case False
        hence id: "(?M = 0) = False" by auto
        let ?c = "((- 1) ^ (degree G3 - degree G4 + 1) * lead_coeff G3 *
            (dichotomous_Lazard (lead_coeff G3) h2 d2) ^ (degree G3 - degree G4))"
        let ?N = "sdiv_poly ?M ?c"
        show ?thesis
        proof (cases "G4 = 0")
          case G4: False
          have "degree ?N \<le> degree ?M" unfolding sdiv_poly_def by (rule degree_map_poly_le)
          also have "\<dots> < degree G4" using pseudo_mod[OF G4, of G3] False by auto
          finally show ?thesis unfolding simp[of G3] Let_def id if_False dl1
            by (intro 1(1)[rule_format], auto)
        next
          case 0: True
          with False have "G3 \<noteq> 0" by auto
          show ?thesis unfolding 0 unfolding simp[of G3] Let_def unfolding dl1 simp[of 0] by simp
        qed
      qed
    qed
  qed
qed

definition [code del]:
  "resultant_impl_rec = subresultant_prs_main_impl (\<lambda> (Gk,hk). if degree Gk = 0 then hk else 0)"
definition [code del]:
  "resultant_impl_start = subresultant_prs_impl (\<lambda> (Gk,hk). if degree Gk = 0 then hk else 0)"
definition [code del]:
  "resultant_impl_Lazard = resultant_impl_main dichotomous_Lazard"

lemma resultant_impl_start_code[code]:
  "resultant_impl_start G1 G2 =
     (let pmod = pseudo_mod G1 G2;
          n2 = degree G2;
          n1 = degree G1;
          g2 = lead_coeff G2;
          d1 = n1 - n2
         in if pmod = 0 then if n2 = 0 then if d1 = 0 then 1 else if d1 = 1 then g2 else g2 ^ d1 else 0
            else let
                 G3 = if even d1 then - pmod else pmod;
                 n3 = degree G3;
                 pmod = pseudo_mod G2 G3
                 in if pmod = 0
                    then if n3 = 0 then
                     let d2 = n2 - n3;
                         g3 = lead_coeff G3
                        in (if d2 = 1 then g3 else
                            dichotomous_Lazard g3 (if d1 = 1 then g2 else g2 ^ d1) d2) else 0
                    else let
                           h2 = (if d1 = 1 then g2 else g2 ^ d1);
                           d2 = n2 - n3;
                           divisor = (if d2 = 1 then g2 * h2 else if even d2 then - g2 * h2 ^ d2 else g2 * h2 ^ d2);
                           G4 = sdiv_poly pmod divisor
                         in resultant_impl_rec G3 G4 n3 d2 h2)"
proof -
  obtain d1 where d1: "degree G1 - degree G2 = d1" by auto
  have id1: "(if even d1 then - pmod else pmod) = (-1)^ (d1 + 1) * (pmod :: 'a poly)" for pmod by simp
  have id3: "(if d2 = 1 then g2 * h2 else if even d2 then - g2 * h2 ^ d2 else g2 * h2 ^ d2) =
    ((- 1) ^ (d2 + 1) * g2 * h2 ^ d2)"
    for d2 and g2 h2 :: 'a by auto
  show ?thesis
    unfolding resultant_impl_start_def subresultant_prs_impl_def resultant_impl_rec_def[symmetric] Let_def split
    unfolding d1
    unfolding id1
    unfolding id3
    by (rule if_cong[OF refl if_cong if_cong], auto simp: power2_eq_square)
qed

lemma resultant_impl_rec_code[code]:
  "resultant_impl_rec Gi_1 Gi ni_1 d1_1 hi_2 = (
    let ni = degree Gi;
        pmod = pseudo_mod Gi_1 Gi
     in
     if pmod = 0
        then if ni = 0
          then
            let
              d1 = ni_1 - ni;
              gi = lead_coeff Gi
            in if d1 = 1 then gi else
              let gi_1 = lead_coeff Gi_1;
                  hi_1 = (if d1_1 = 1 then gi_1 else dichotomous_Lazard gi_1 hi_2 d1_1) in
                dichotomous_Lazard gi hi_1 d1
          else 0
        else let
           d1 = ni_1 - ni;
           gi_1 = lead_coeff Gi_1;
           hi_1 = (if d1_1 = 1 then gi_1 else dichotomous_Lazard gi_1 hi_2 d1_1);
           divisor = if d1 = 1 then gi_1 * hi_1 else if even d1 then - gi_1 * hi_1 ^ d1 else gi_1 * hi_1 ^ d1;
           Gi_p1 = sdiv_poly pmod divisor
       in resultant_impl_rec Gi Gi_p1 ni d1 hi_1)"
  unfolding resultant_impl_rec_def subresultant_prs_main_impl.simps[of _ Gi_1] split Let_def
  unfolding resultant_impl_rec_def[symmetric]
  by (rule if_cong[OF _ if_cong _], auto)

lemma resultant_impl_Lazard_code[code]: "resultant_impl_Lazard G1 G2 =
  (if G2 = 0 then if degree G1 = 0 then 1 else 0
     else resultant_impl_start G1 G2)"
  unfolding resultant_impl_Lazard_def resultant_impl_main_def
   resultant_impl_start_def subresultant_prs_impl by simp

lemma resultant_impl_code[code]: "resultant_impl f g =
  (if length (coeffs f) \<ge> length (coeffs g) then resultant_impl_Lazard f g
     else let res = resultant_impl_Lazard g f in
      if even (degree f) \<or> even (degree g) then res else - res)"
  unfolding resultant_impl_def resultant_impl_generic_def resultant_impl_Lazard_def ..

lemma resultant_code[code]: "resultant f g = resultant_impl f g" by simp

end