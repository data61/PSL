(*
  File:     Finite_Fourier_Series.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  Existence and uniqueness of finite Fourier series for periodic arithmetic functions
*)
section \<open>Finite Fourier series\<close>
theory Finite_Fourier_Series
imports 
  Polynomial_Interpolation.Lagrange_Interpolation
  Complex_Roots_Of_Unity
begin

subsection \<open>Auxiliary facts\<close>

lemma lagrange_exists:
  assumes d: "distinct (map fst zs_ws)"
  defines e: "(p :: complex poly) \<equiv> lagrange_interpolation_poly zs_ws"
  shows "degree p \<le> (length zs_ws)-1"
        "(\<forall>x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y)" 
proof -
  from e show "degree p \<le> (length zs_ws - 1)"
    using degree_lagrange_interpolation_poly by auto
  from e d have 
    "poly p x = y" if "(x,y) \<in> set zs_ws" for x y 
    using that lagrange_interpolation_poly by auto
  then show "(\<forall>x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y)" 
    by auto
qed

lemma lagrange_unique:
  assumes o: "length zs_ws > 0" (* implicit in theorem *)
  assumes d: "distinct (map fst zs_ws)"
  assumes 1: "degree (p1 :: complex poly) \<le> (length zs_ws)-1 \<and>
               (\<forall>x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p1 x = y)"
  assumes 2: "degree (p2 :: complex poly) \<le> (length zs_ws)-1 \<and>
               (\<forall>x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p2 x = y)"
  shows "p1 = p2" 
proof (cases "p1 - p2 = 0")
  case True then show ?thesis by simp
next
  case False
    have "poly (p1-p2) x = 0" if "x \<in> set (map fst zs_ws)" for x
      using 1 2 that by (auto simp add: field_simps)
    from this d have 3: "card {x. poly (p1-p2) x = 0} \<ge> length zs_ws"
    proof (induction zs_ws)
      case Nil then show ?case by simp
    next
      case (Cons z_w zs_ws)
      from  False poly_roots_finite
      have f: "finite {x. poly (p1 - p2) x = 0}" by blast
      from Cons have "set (map fst (z_w # zs_ws)) \<subseteq> {x. poly (p1 - p2) x = 0}"
        by auto
      then have i: "card (set (map fst (z_w # zs_ws))) \<le> card {x. poly (p1 - p2) x = 0}" 
        using card_mono f by blast
      have "length (z_w # zs_ws) \<le> card (set (map fst (z_w # zs_ws)))"
        using Cons.prems(2) distinct_card by fastforce 
      from this i show ?case by simp 
    qed
    from 1 2 have 4: "degree (p1 - p2) \<le> (length zs_ws)-1" 
      using degree_diff_le by blast
 
    have "p1 - p2 = 0"  
    proof (rule ccontr)
      assume "p1 - p2 \<noteq> 0"
      then have "card {x. poly (p1-p2) x = 0} \<le> degree (p1-p2)"
        using poly_roots_degree by blast
      then have "card {x. poly (p1-p2) x = 0} \<le> (length zs_ws)-1"
        using 4 by auto
      then show "False" using 3 o by linarith
    qed
    then show ?thesis by simp 
qed

text \<open>Theorem 8.2\<close>
corollary lagrange:
  assumes "length zs_ws > 0" "distinct (map fst zs_ws)"
  shows "(\<exists>! (p :: complex poly).
              degree p \<le> length zs_ws - 1 \<and>
              (\<forall>x y. (x, y) \<in> set zs_ws \<longrightarrow> poly p x = y))"
  using assms lagrange_exists lagrange_unique by blast

lemma poly_altdef':
 assumes gr: "k \<ge> degree p"  
 shows "poly p (z::complex) = (\<Sum>i\<le>k. coeff p i * z ^ i)"
proof -
  {fix z
  have 1: "poly p z = (\<Sum>i\<le>degree p. coeff p i * z ^ i)"
    using poly_altdef[of p z] by simp
  have "poly p z = (\<Sum>i\<le>k. coeff p i * z ^ i)" 
    using gr
  proof (induction k)
    case 0 then show ?case by (simp add: poly_altdef) 
  next
    case (Suc k) 
    then show ?case
      using "1" le_degree not_less_eq_eq by fastforce
  qed}  
  then show ?thesis using gr by blast 
qed


subsection \<open>Definition and uniqueness\<close>

definition finite_fourier_poly :: "complex list \<Rightarrow> complex poly" where
  "finite_fourier_poly ws =
    (let k = length ws
      in  poly_of_list [1 / k * (\<Sum>m<k. ws ! m * unity_root k (-n*m)). n \<leftarrow> [0..<k]])"

lemma degree_poly_of_list_le: "degree (poly_of_list ws) \<le> length ws - 1"
  by (intro degree_le) (auto simp: nth_default_def)

lemma degree_finite_fourier_poly: "degree (finite_fourier_poly ws) \<le> length ws - 1"
  unfolding finite_fourier_poly_def
proof (subst Let_def)
  let ?unrolled_list = "
       (map (\<lambda>n. complex_of_real (1 / real (length ws)) *
                  (\<Sum>m<length ws.
                      ws ! m *
                      unity_root (length ws) (- int n * int m)))
         [0..<length ws])"
  have "degree (poly_of_list ?unrolled_list) \<le> length ?unrolled_list - 1"   
    by (rule degree_poly_of_list_le)
  also have "\<dots> = length [0..<length ws] - 1"
    using length_map by auto
  also have "\<dots> = length ws - 1" by auto
  finally show "degree (poly_of_list ?unrolled_list) \<le> length ws - 1" by blast
qed

lemma coeff_finite_fourier_poly:
  assumes "n < length ws"
  defines "k \<equiv> length ws"
  shows "coeff (finite_fourier_poly ws) n = 
         (1/k) * (\<Sum>m < k. ws ! m * unity_root k (-n*m))"
  using assms degree_finite_fourier_poly
  by (auto simp: Let_def nth_default_def finite_fourier_poly_def)

lemma poly_finite_fourier_poly:
  fixes m :: int and ws
  defines "k \<equiv> length ws"
  assumes "m \<in> {0..<k}"
  assumes "m < length ws"
  shows "poly (finite_fourier_poly ws) (unity_root k m) = ws ! (nat m)"
proof -
  have "k > 0" using assms by auto

  have distr: "
   (\<Sum>j<length ws. ws ! j * unity_root k (-i*j))*(unity_root k (m*i)) = 
   (\<Sum>j<length ws. ws ! j * unity_root k (-i*j)*(unity_root k (m*i)))"
   for i
  using sum_distrib_right[of "\<lambda>j. ws ! j * unity_root k (-i*j)" 
                            "{..<k}" "(unity_root k (m*i))"] 
  using k_def by blast

  {fix j i :: nat
   have "unity_root k (-i*j)*(unity_root k (m*i)) = unity_root k (-i*j+m*i)"
     by (simp add: unity_root_diff unity_root_uminus field_simps)
   also have "\<dots> = unity_root k (i*(m-j))"
     by (simp add: algebra_simps)
   finally have "unity_root k (-i*j)*(unity_root k (m*i)) = unity_root k (i*(m-j))"
     by simp
   then have "ws ! j * unity_root k (-i*j)*(unity_root k (m*i)) = 
              ws ! j * unity_root k (i*(m-j))"
     by auto
 } note prod = this

 have zeros: 
   "(unity_root_sum k (m-j) \<noteq> 0 \<longleftrightarrow> m = j)
     " if "j \<ge> 0 \<and> j < k"  for j
   using k_def that assms unity_root_sum_nonzero_iff[of _ "m-j"] by simp
  then have sum_eq:
    "(\<Sum>j\<le>k-1. ws ! j * unity_root_sum k (m-j)) = 
          (\<Sum>j\<in>{nat m}.  ws ! j * unity_root_sum k (m-j))"
    using assms(2) by (intro sum.mono_neutral_right,auto)

  have "poly (finite_fourier_poly ws) (unity_root k m) = 
        (\<Sum>i\<le>k-1. coeff (finite_fourier_poly ws) i * (unity_root k m) ^ i)"
    using degree_finite_fourier_poly[of ws] k_def
          poly_altdef'[of "finite_fourier_poly ws" "k-1" "unity_root k m"] by blast
  also have "\<dots> = (\<Sum>i<k. coeff (finite_fourier_poly ws) i * (unity_root k m) ^ i)"
    using assms(2) by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j)) * (unity_root k m) ^ i)"
    using coeff_finite_fourier_poly[of _ ws] k_def by auto
  also have "\<dots> = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j))*(unity_root k (m*i)))"
    using unity_root_pow by auto   
  also have "\<dots> = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j)*(unity_root k (m*i))))"
    using distr k_def by simp
  also have "\<dots> = (\<Sum>i<k. 1 / k * 
    (\<Sum>j<k. ws ! j * unity_root k (i*(m-j))))"
    using prod by presburger
  also have "\<dots> = 1 / k * (\<Sum>i<k.  
    (\<Sum>j<k. ws ! j * unity_root k (i*(m-j))))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = 1 / k * (\<Sum>j<k.  
    (\<Sum>i<k. ws ! j * unity_root k (i*(m-j))))"
    using sum.swap by fastforce
  also have "\<dots> = 1 / k * (\<Sum>j<k. ws ! j * (\<Sum>i<k. unity_root k (i*(m-j))))"
    by (simp add: vector_space_over_itself.scale_sum_right)
  also have "\<dots> = 1 / k * (\<Sum>j<k. ws ! j * unity_root_sum k (m-j))"
    unfolding unity_root_sum_def by (simp add: algebra_simps)
  also have "(\<Sum>j<k. ws ! j * unity_root_sum k (m-j)) = (\<Sum>j\<le>k-1. ws ! j * unity_root_sum k (m-j))"
    using \<open>k > 0\<close> by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>j\<in>{nat m}.  ws ! j * unity_root_sum k (m-j))"
    using sum_eq .
  also have "\<dots> = ws ! (nat m) * k"
    using assms(2) by (auto simp: algebra_simps)
  finally have "poly (finite_fourier_poly ws) (unity_root k m) = ws ! (nat m)"
    using assms(2) by auto
  then show ?thesis by simp
qed

text \<open>Theorem 8.3\<close>
theorem finite_fourier_poly_unique:
  assumes "length ws > 0"
  defines "k \<equiv> length ws"
  assumes "(degree p \<le> k - 1)"
  assumes "(\<forall>m \<le> k-1. (ws ! m) = poly p (unity_root k m))"
  shows "p = finite_fourier_poly ws"
proof -  
  let ?z = "map (\<lambda>m. unity_root k m) [0..<k]" 
  have k: "k > 0" using assms by auto
  from k have d1: "distinct ?z"
    unfolding distinct_conv_nth using unity_root_eqD[OF k] by force  
  let ?zs_ws = "zip ?z ws"
  from d1 k_def have d2: "distinct (map fst ?zs_ws)" by simp
  have l2: "length ?zs_ws > 0" using assms(1) k_def by auto
  have l3: "length ?zs_ws = k" by (simp add: k_def)

  from degree_finite_fourier_poly have degree: "degree (finite_fourier_poly ws) \<le> k - 1" 
    using k_def by simp

  have interp: "poly (finite_fourier_poly ws) x = y"
    if "(x, y) \<in> set ?zs_ws" for x y
  proof -
    from that obtain n where "
         x = map (unity_root k \<circ> int) [0..<k] ! n \<and>
         y = ws ! n \<and> 
         n < length ws"
      using in_set_zip[of "(x,y)" "(map (unity_root k) (map int [0..<k]))" ws]
      by auto
    then have "
         x = unity_root k (int n) \<and>
         y = ws ! n \<and> 
         n < length ws"
      using nth_map[of n "[0..<k]" "unity_root k \<circ> int" ] k_def by simp
    thus "poly (finite_fourier_poly ws) x = y"
      by (simp add: poly_finite_fourier_poly k_def)
  qed

  have interp_p: "poly p x = y" if "(x,y) \<in> set ?zs_ws" for x y
  proof -
    from that obtain n where "
         x = map (unity_root k \<circ> int) [0..<k] ! n \<and>
         y = ws ! n \<and> 
         n < length ws"
      using in_set_zip[of "(x,y)" "(map (unity_root k) (map int [0..<k]))" ws]
      by auto
    then have rw: "x = unity_root k (int n)" "y = ws ! n" "n < length ws"
      using nth_map[of n "[0..<k]" "unity_root k \<circ> int" ] k_def by simp+
    show "poly p x = y" 
      unfolding rw(1,2) using assms(4) rw(3) k_def by simp
  qed

  from lagrange_unique[of _ p "finite_fourier_poly ws"] d2 l2
  have l: "
    degree p \<le> k - 1 \<and>
    (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly p x = y) \<Longrightarrow>
    degree (finite_fourier_poly ws) \<le> k - 1 \<and>
    (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly (finite_fourier_poly ws) x = y) \<Longrightarrow>
    p = (finite_fourier_poly ws)"
    using l3 by fastforce
  from assms degree interp interp_p l3
  show "p = (finite_fourier_poly ws)" using l by blast  
qed


text \<open>
  The following alternative formulation returns a coefficient
\<close>
definition finite_fourier_poly' :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex poly" where
  "finite_fourier_poly' ws k =
     (poly_of_list [1 / k * (\<Sum>m<k. (ws m) * unity_root k (-n*m)). n \<leftarrow> [0..<k]])"

lemma finite_fourier_poly'_conv_finite_fourier_poly:
  "finite_fourier_poly' ws k = finite_fourier_poly [ws n. n \<leftarrow> [0..<k]]"
  unfolding finite_fourier_poly_def finite_fourier_poly'_def by simp

lemma coeff_finite_fourier_poly': 
  assumes "n < k"
  shows "coeff (finite_fourier_poly' ws k) n = 
         (1/k) * (\<Sum>m < k. (ws m) * unity_root k (-n*m))"
proof -
  let ?ws = "[ws n. n \<leftarrow> [0..<k]]"
  have "coeff (finite_fourier_poly' ws k) n =
        coeff (finite_fourier_poly ?ws) n" 
    by (simp add: finite_fourier_poly'_conv_finite_fourier_poly)
  also have "coeff (finite_fourier_poly ?ws) n = 
    1 / k * (\<Sum>m<k. (?ws ! m) * unity_root k (- n*m))" 
    using assms by (auto simp: coeff_finite_fourier_poly)
  also have "\<dots> = (1/k) * (\<Sum>m < k. (ws m) * unity_root k (-n*m))"
    using assms by simp
  finally show ?thesis by simp    
qed

lemma degree_finite_fourier_poly': "degree (finite_fourier_poly' ws k) \<le> k - 1"
  using degree_finite_fourier_poly[of "[ws n. n \<leftarrow> [0..<k]]"]
  by (auto simp: finite_fourier_poly'_conv_finite_fourier_poly)

lemma poly_finite_fourier_poly':
  fixes m :: int and k
  assumes "m \<in> {0..<k}"
  shows "poly (finite_fourier_poly' ws k) (unity_root k m) = ws (nat m)"
  using assms poly_finite_fourier_poly[of m "[ws n. n \<leftarrow> [0..<k]]"]
  by (auto simp: finite_fourier_poly'_conv_finite_fourier_poly poly_finite_fourier_poly)

lemma finite_fourier_poly'_unique:
  assumes "k > 0"
  assumes "degree p \<le> k - 1"
  assumes "\<forall>m\<le>k-1. ws m = poly p (unity_root k m)"
  shows "p = finite_fourier_poly' ws k"
proof -
  let ?ws = "[ws n. n \<leftarrow> [0..<k]]"
  from finite_fourier_poly_unique have "p = finite_fourier_poly ?ws" using assms by simp
  also have "\<dots> = finite_fourier_poly' ws k"
    using finite_fourier_poly'_conv_finite_fourier_poly ..
  finally show "p = finite_fourier_poly' ws k" by blast
qed

lemma fourier_unity_root:
  fixes k :: nat
  assumes "k > 0" 
  shows "poly (finite_fourier_poly' f k) (unity_root k m) = 
    (\<Sum>n<k.1/k*(\<Sum>m<k.(f m)*unity_root k (-n*m))*unity_root k (m*n))"
proof -
  have "poly (finite_fourier_poly' f k) (unity_root k m) = 
        (\<Sum>n\<le>k-1. coeff (finite_fourier_poly' f k) n *(unity_root k m)^n)"
    using poly_altdef'[of "finite_fourier_poly' f k" "k-1" "unity_root k m"]
          degree_finite_fourier_poly'[of f k] by simp
  also have "\<dots> = (\<Sum>n\<le>k-1. coeff (finite_fourier_poly' f k) n *(unity_root k (m*n)))" 
    using unity_root_pow by simp
  also have "\<dots> = (\<Sum>n<k. coeff (finite_fourier_poly' f k) n *(unity_root k (m*n)))" 
    using assms by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>n<k.(1/k)*(\<Sum>m<k.(f m)*unity_root k (-n*m))*(unity_root k (m*n)))" 
    using coeff_finite_fourier_poly'[of _ k f] by simp
  finally show
   "poly (finite_fourier_poly' f k) (unity_root k m) = 
    (\<Sum>n<k.1/k*(\<Sum>m<k.(f m)*unity_root k (-n*m))*unity_root k (m*n))"
    by blast
qed
  
subsection \<open>Expansion of an arithmetical function\<close>

text \<open>Theorem 8.4\<close>
theorem fourier_expansion_periodic_arithmetic:
  assumes "k > 0"
  assumes "periodic_arithmetic f k"
  defines "g \<equiv> (\<lambda>n. (1 / k) * (\<Sum>m<k. f m * unity_root k (-n * m)))"
    shows "periodic_arithmetic g k" 
      and "f m = (\<Sum>n<k. g n * unity_root k (m * n))"  
proof -
 {fix l
  from unity_periodic_arithmetic mult_period
  have period: "periodic_arithmetic (\<lambda>x. unity_root k x) (k*l)" by simp}
  note period = this
 {fix n l
  have "unity_root k (-(n+k)*l) = cnj (unity_root k ((n+k)*l))"
    by (simp add: unity_root_uminus unity_root_diff ring_distribs unity_root_add)
  also have "unity_root k ((n+k)*l) = unity_root k (n*l)"
    by (intro unity_root_cong) (auto simp: cong_def algebra_simps)
  also have "cnj \<dots> = unity_root k (-n*l)"
    using unity_root_uminus by simp 
  finally have "unity_root k (-(n+k)*l) = unity_root k (-n*l)" by simp}
  note u_period = this
  
  show 1: "periodic_arithmetic g k"
    unfolding periodic_arithmetic_def
  proof 
    fix n 
   
    have "g(n+k) = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-(n+k)*m))"
      using assms(3) by fastforce
    also have "\<dots> = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"
    proof -
      have "(\<Sum>m<k. f(m) * unity_root k (-(n+k)*m)) = 
            (\<Sum>m<k. f(m) * unity_root k (-n*m))" 
        by (intro sum.cong) (use u_period in auto)
      then show ?thesis by argo
    qed
    also have "\<dots> = g(n)"
      using assms(3) by fastforce
    finally show "g(n+k) = g(n)" by simp 
  qed

  show "f(m) = (\<Sum>n<k. g(n)* unity_root k (m * int n))"
  proof -
    { 
      fix m
      assume range: "m \<in> {0..<k}"
      have "f(m) = (\<Sum>n<k. g(n)* unity_root k (m * int n))"
      proof -
        have "f m = poly (finite_fourier_poly' f k) (unity_root k m)"
          using range by (simp add: poly_finite_fourier_poly')
        also have "\<dots> = (\<Sum>n<k. (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))* unity_root k (m*n))"
          using fourier_unity_root assms(1) by blast
        also have "\<dots> = (\<Sum>n<k. g(n)* unity_root k (m*n))"
          using assms by simp
        finally show ?thesis by auto
    qed}
  note concentrated = this

  have "periodic_arithmetic (\<lambda>m. (\<Sum>n<k. g(n)* unity_root k (m * int n))) k"
  proof - 
    have "periodic_arithmetic (\<lambda>n. g(n)* unity_root k (i * int n)) k"  for i :: int
      using 1 unity_periodic_arithmetic mult_periodic_arithmetic
            unity_periodic_arithmetic_mult by auto
    then have p_s: "\<forall>i<k. periodic_arithmetic (\<lambda>n. g(n)* unity_root k (i * int n)) k"
      by simp
    have "periodic_arithmetic (\<lambda>i. \<Sum>n<k. g(n)* unity_root k (i * int n)) k"
      unfolding periodic_arithmetic_def
    proof
      fix n
      show "(\<Sum>na<k. g na * unity_root k (int (n + k) * int na)) =
            (\<Sum>na<k. g na * unity_root k (int n * int na))"      
        by (intro sum.cong refl, simp add: distrib_right flip: of_nat_mult of_nat_add)
           (insert period, unfold periodic_arithmetic_def, blast)
    qed
    then show ?thesis by simp
  qed  
  
  from this assms(1-2) concentrated 
       unique_periodic_arithmetic_extension[of k f "(\<lambda>i. \<Sum>n<k. g(n)* unity_root k (i * int n))"  m]
  show "f m = (\<Sum>n<k. g n * unity_root k (int m * int n))" by simp        
  qed
qed

theorem fourier_expansion_periodic_arithmetic_unique:
  fixes f g :: "nat \<Rightarrow> complex" 
  assumes "k > 0"
  assumes "periodic_arithmetic f k" and "periodic_arithmetic g k"
  assumes "\<And>m. m < k \<Longrightarrow> f m = (\<Sum>n<k. g n * unity_root k (int (m * n)))" 
  shows   "g n = (1 / k) * (\<Sum>m<k. f m * unity_root k (-n * m))"
proof -
  let ?p = "poly_of_list [g(n). n \<leftarrow> [0..<k]]"
  have d: "degree ?p \<le> k-1"
  proof -
    have "degree ?p \<le> length [g(n). n \<leftarrow> [0..<k]] - 1" 
      using degree_poly_of_list_le by blast
    also have "\<dots> = length [0..<k] - 1" 
      using length_map by auto
    finally show ?thesis by simp
  qed    
  have c: "coeff ?p i = (if i < k then g(i) else 0)" for i
    by (simp add: nth_default_def)
  {fix z
  have "poly ?p z = (\<Sum>n\<le>k-1. coeff ?p n* z^n)" 
    using poly_altdef'[of ?p "k-1"] d by blast
  also have "\<dots> = (\<Sum>n<k. coeff ?p n* z^n)" 
    using \<open>k > 0\<close> by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>n<k. (if n < k then g(n) else 0)* z^n)"
    using c by simp
  also have "\<dots> = (\<Sum>n<k. g(n)* z^n)" 
    by (simp split: if_splits)
  finally have "poly ?p z = (\<Sum>n<k. g n * z ^ n)" .}
  note eval = this
  {fix i
  have "poly ?p (unity_root k i) = (\<Sum>n<k. g(n)* (unity_root k i)^n)"
    using eval by blast
  then have "poly ?p (unity_root k i) = (\<Sum>n<k. g(n)* (unity_root k (i*n)))"
    using unity_root_pow by auto}
  note interpolation = this

  {
    fix m 
    assume b: "m \<le> k-1"
    from d assms(1)
    have "f m = (\<Sum>n<k. g(n) * unity_root k (m*n))" 
      using assms(4) b by auto 
    also have "\<dots> = poly ?p (unity_root k m)"
      using interpolation by simp
    finally have "f m = poly ?p (unity_root k m)" by auto
  }

  from this finite_fourier_poly'_unique[of k _ f]
  have p_is_fourier: "?p = finite_fourier_poly' f k"
    using assms(1) d by blast

  {
    fix n 
    assume b: "n \<le> k-1"
    have f_1: "coeff ?p n = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"  
      using p_is_fourier using assms(1) b by (auto simp: coeff_finite_fourier_poly')
    then have "g(n) = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"
      using c b assms(1) 
    proof -
      have 1: "coeff ?p n = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"
        using f_1 by blast
      have 2: "coeff ?p n =  g n"
        using c assms(1) b by simp
      show ?thesis using 1 2 by argo
    qed
  }

 (* now show right hand side is periodic and use unique_periodic_extension *)
  have "periodic_arithmetic (\<lambda>n. (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))) k"
  proof - 
    have "periodic_arithmetic (\<lambda>i. unity_root k (-int i*int m)) k" for m
      using unity_root_periodic_arithmetic_mult_minus by simp
    then have "periodic_arithmetic (\<lambda>i. f(m) * unity_root k (-i*m)) k" for m
      by (simp add: periodic_arithmetic_def)
    then show "periodic_arithmetic (\<lambda>i. (1 / k) * (\<Sum>m<k. f m * unity_root k (-i*m))) k"
      by (intro scalar_mult_periodic_arithmetic fin_sum_periodic_arithmetic_set) auto
  qed
  note periodich = this
  let ?h = "(\<lambda>i. (1 / k) *(\<Sum>m<k. f m * unity_root k (-i*m)))"
  from unique_periodic_arithmetic_extension[of k g ?h n] 
        assms(3) assms(1) periodich
  have "g n = (1/k) * (\<Sum>m<k. f m * unity_root k (-n*m))" 
    by (simp add: \<open>\<And>na. na \<le> k - 1 \<Longrightarrow> g na = complex_of_real (1 / real k) * (\<Sum>m<k. f m * unity_root k (- int na * int m))\<close>)
  then show ?thesis by simp
qed

end