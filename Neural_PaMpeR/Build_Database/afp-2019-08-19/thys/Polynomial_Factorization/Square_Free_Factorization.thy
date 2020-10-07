(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Square Free Factorization\<close>

text \<open>We implemented Yun's algorithm to perform a square-free factorization of a polynomial.
We further show properties of a square-free factorization, namely that the exponents in
the square-free factorization are exactly the orders of the roots. We also show that 
factorizing the result of square-free factorization further will again result in a 
square-free factorization, and that square-free factorizations can be lifted homomorphically.\<close>

theory Square_Free_Factorization
imports 
  Matrix.Utility
  Polynomial_Divisibility
  Order_Polynomial
  Fundamental_Theorem_Algebra_Factorized
  Polynomial_Interpolation.Ring_Hom_Poly
begin

definition square_free :: "'a :: comm_semiring_1 poly \<Rightarrow> bool" where 
  "square_free p = (p \<noteq> 0 \<and> (\<forall> q. degree q > 0 \<longrightarrow> \<not> (q * q dvd p)))"

lemma square_freeI:  
  assumes "\<And> q. degree q > 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> q * q dvd p \<Longrightarrow> False"
  and p: "p \<noteq> 0"
  shows "square_free p" unfolding square_free_def
proof (intro allI conjI[OF p] impI notI, goal_cases)
  case (1 q)
  from assms(1)[OF 1(1) _ 1(2)] 1(1) show False by (cases "q = 0", auto)
qed

lemma square_free_multD:
  assumes sf: "square_free (f * g)"
  shows "h dvd f \<Longrightarrow> h dvd g \<Longrightarrow> degree h = 0" "square_free f" "square_free g"
proof -
  from sf[unfolded square_free_def] have 0: "f \<noteq> 0" "g \<noteq> 0"
    and dvd: "\<And> q. q * q dvd f * g \<Longrightarrow> degree q = 0" by auto
  then show "square_free f" "square_free g" by (auto simp: square_free_def)
  assume "h dvd f" "h dvd g"
  then have "h * h dvd f * g" by (rule mult_dvd_mono)
  from dvd[OF this] show "degree h = 0".
qed

lemma irreducible\<^sub>d_square_free:
  fixes p :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} poly"
  shows "irreducible\<^sub>d p \<Longrightarrow> square_free p"
  by (metis degree_0 degree_mult_eq degree_mult_eq_0 irreducible\<^sub>dD(1) irreducible\<^sub>dD(2) irreducible\<^sub>d_dvd_smult irreducible\<^sub>d_smultI less_add_same_cancel2 not_gr_zero square_free_def)

lemma square_free_factor: assumes dvd: "a dvd p"
  and sf: "square_free p"
  shows "square_free a"
proof (intro square_freeI)
  fix q
  assume q: "degree q > 0" and "q * q dvd a"
  hence "q * q dvd p" using dvd dvd_trans sf square_free_def by blast
  with sf[unfolded square_free_def] q show False by auto
qed (insert dvd sf, auto simp: square_free_def)

lemma square_free_prod_list_distinct: 
  assumes sf: "square_free (prod_list us :: 'a :: idom poly)"
  and us: "\<And> u. u \<in> set us \<Longrightarrow> degree u > 0"
  shows "distinct us"
proof (rule ccontr)
  assume "\<not> distinct us"
  from not_distinct_decomp[OF this] obtain xs ys zs u where
     "us = xs @ u # ys @ u # zs" by auto
  hence dvd: "u * u dvd prod_list us" and u: "u \<in> set us" by auto
  from dvd us[OF u] sf have "prod_list us = 0" unfolding square_free_def by auto
  hence "0 \<in> set us" by (simp add: prod_list_zero_iff)
  from us[OF this] show False by auto
qed

definition separable where 
  "separable f = coprime f (pderiv f)" 

lemma separable_imp_square_free:
  assumes sep: "separable (f :: 'a::{field, factorial_ring_gcd} poly)" 
  shows "square_free f" 
proof (rule ccontr)
  note sep = sep[unfolded separable_def]
  from sep have f0: "f \<noteq> 0" by (cases f, auto)
  assume "\<not> square_free f"
  then obtain g where g: "degree g \<noteq> 0" and "g * g dvd f" using f0 unfolding square_free_def by auto
  then obtain h where f: "f = g * (g * h)" unfolding dvd_def by (auto simp: ac_simps)
  have "pderiv f = g * ((g * pderiv h + h * pderiv g) + h * pderiv g)" 
    unfolding f pderiv_mult[of g] by (simp add: field_simps)
  hence "g dvd pderiv f" unfolding dvd_def by blast
  moreover have "g dvd f" unfolding f dvd_def by blast
  ultimately have dvd: "g dvd (gcd f (pderiv f))" by simp
  have "gcd f (pderiv f) \<noteq> 0" using f0 by simp
  with g dvd have "degree (gcd f (pderiv f)) \<noteq> 0"
    by (simp add: sep poly_dvd_1)
  hence "\<not> coprime f (pderiv f)" by auto
  with sep show False by simp
qed

lemma square_free_rsquarefree: assumes f: "square_free f" 
  shows "rsquarefree f"
  unfolding rsquarefree_def
proof (intro conjI allI)
  fix x
  show "order x f = 0 \<or> order x f = 1"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain n where ord: "order x f = Suc (Suc n)" 
      by (cases "order x f"; cases "order x f - 1"; auto)
    define p where "p = [:-x,1:]"
    from order_divides[of x "Suc (Suc 0)" f, unfolded ord]
    have "p * p dvd f" "degree p \<noteq> 0" unfolding p_def by auto
    hence "\<not> square_free f" using f(1) unfolding square_free_def by auto
    with assms show False by auto
  qed
qed (insert f, auto simp: square_free_def)

lemma square_free_prodD: 
  fixes fs :: "'a :: {field,euclidean_ring_gcd} poly set"
  assumes sf: "square_free (\<Prod> fs)"
  and fin: "finite fs"
  and f: "f \<in> fs"
  and g: "g \<in> fs"
  and fg: "f \<noteq> g"
  shows "coprime f g"
proof -
  have "(\<Prod> fs) = f * (\<Prod> (fs - {f}))"
    by (rule prod.remove[OF fin f])
  also have "(\<Prod> (fs - {f})) = g * (\<Prod> (fs - {f} - {g}))"
    by (rule prod.remove, insert fin g fg, auto)
  finally obtain k where sf: "square_free (f * g * k)" using sf by (simp add: ac_simps)
  from sf[unfolded square_free_def] have 0: "f \<noteq> 0" "g \<noteq> 0" 
    and dvd: "\<And> q. q * q dvd f * g * k \<Longrightarrow> degree q = 0"
    by auto
  have "gcd f g * gcd f g dvd f * g * k" by (simp add: mult_dvd_mono)
  from dvd[OF this] have "degree (gcd f g) = 0" . 
  moreover have "gcd f g \<noteq> 0" using 0 by auto
  ultimately show "coprime f g" using is_unit_gcd[of f g] is_unit_iff_degree[of "gcd f g"] by simp    
qed

lemma rsquarefree_square_free_complex: assumes "rsquarefree (p :: complex poly)"
  shows "square_free p"
proof (rule square_freeI)
  fix q
  assume d: "degree q > 0" and dvd: "q * q dvd p"
  from d have "\<not> constant (poly q)" by (simp add: constant_degree)
  from fundamental_theorem_of_algebra[OF this] obtain x where "poly q x = 0" by auto
  hence "[:-x,1:] dvd q" by (simp add: poly_eq_0_iff_dvd)
  then obtain k where q: "q = [:-x,1:] * k" unfolding dvd_def by auto
  from dvd obtain l where p: "p = q * q * l" unfolding dvd_def by auto
  from p[unfolded q] have "p = [:-x,1:]^2 * (k * k * l)" by algebra
  hence "[:-x,1:]^2 dvd p" unfolding dvd_def by blast
  from this[unfolded order_divides] have "p = 0 \<or> \<not> order x p \<le> 1" by auto
  thus False using assms unfolding rsquarefree_def' by auto
qed (insert assms, auto simp: rsquarefree_def)
   
lemma square_free_separable_main:
  fixes f :: "'a :: {field,factorial_ring_gcd} poly"
  assumes "square_free f"
  and sep: "\<not> separable f"
  shows "\<exists> g k. f = g * k \<and> degree g \<noteq> 0 \<and> pderiv g = 0"
proof -
  note cop = sep[unfolded separable_def]
  from assms have f: "f \<noteq> 0" unfolding square_free_def by auto
  let ?g = "gcd f (pderiv f)"
  define G where "G = ?g"
  from poly_gcd_monic[of f "pderiv f"] f have mon: "monic ?g"
    by auto
  have deg: "degree G > 0" 
  proof (cases "degree G")
    case 0
    from degree0_coeffs[OF this] cop mon show ?thesis
      by (auto simp: G_def coprime_iff_gcd_eq_1)
  qed auto
  have gf: "G dvd f" unfolding G_def by auto
  have gf': "G dvd pderiv f" unfolding G_def by auto
  from irreducible\<^sub>d_factor[OF deg] obtain g r where g: "irreducible g" and G: "G = g * r" by auto
  from gf have gf: "g dvd f" unfolding G by (rule dvd_mult_left)
  from gf' have gf': "g dvd pderiv f" unfolding G by (rule dvd_mult_left)
  have g0: "degree g \<noteq> 0" using g unfolding irreducible\<^sub>d_def by auto
  from gf obtain k where fgk: "f = g * k" unfolding dvd_def by auto
  have id1: "pderiv f = g * pderiv k + k * pderiv g" unfolding fgk pderiv_mult by simp
  from gf' obtain h where "pderiv f = g * h" unfolding dvd_def by auto
  from id1[unfolded this] have "k * pderiv g = g * (h - pderiv k)" by (simp add: field_simps)
  hence dvd: "g dvd k * pderiv g" unfolding dvd_def by auto
  {
    assume "g dvd k" 
    then obtain h where k: "k = g * h" unfolding dvd_def by auto
    with fgk have "g * g dvd f" by auto
    with g0 have "\<not> square_free f" unfolding square_free_def using f by auto
    with assms have False by simp
  }
  with  g dvd 
  have "g dvd pderiv g" by auto
  from divides_degree[OF this] degree_pderiv_le[of g] g0
  have "pderiv g = 0" by linarith
  with fgk g0 show ?thesis by auto
qed

lemma square_free_imp_separable: fixes f :: "'a :: {field_char_0,factorial_ring_gcd} poly"
  assumes "square_free f"
  shows "separable f"
proof (rule ccontr)
  assume "\<not> separable f" 
  from square_free_separable_main[OF assms this]
  obtain g k where *: "f = g * k" "degree g \<noteq> 0" "pderiv g = 0" by auto
  hence "g dvd pderiv g" by auto
  thus False unfolding dvd_pderiv_iff using * by auto
qed
   

lemma square_free_iff_separable: 
  "square_free (f :: 'a :: {field_char_0,factorial_ring_gcd} poly) = separable f"
  using separable_imp_square_free[of f] square_free_imp_separable[of f] by auto

context
  assumes "SORT_CONSTRAINT('a::{field,factorial_ring_gcd})"
begin
lemma square_free_smult: "c \<noteq> 0 \<Longrightarrow> square_free (f :: 'a poly) \<Longrightarrow> square_free (smult c f)"
  by (unfold square_free_def, insert dvd_smult_cancel[of _ c], auto)

lemma square_free_smult_iff[simp]: "c \<noteq> 0 \<Longrightarrow> square_free (smult c f) = square_free (f :: 'a poly)"
  using square_free_smult[of c f] square_free_smult[of "inverse c" "smult c f"] by auto
end

context
  assumes "SORT_CONSTRAINT('a::factorial_ring_gcd)"
begin
definition square_free_factorization :: "'a poly \<Rightarrow> 'a \<times> ('a poly \<times> nat) list \<Rightarrow> bool" where
  "square_free_factorization p cbs \<equiv> case cbs of (c,bs) \<Rightarrow>
    (p = smult c (\<Prod>(a, i)\<in> set bs. a ^ Suc i))
  \<and> (p = 0 \<longrightarrow> c = 0 \<and> bs = [])
  \<and> (\<forall> a i. (a,i) \<in> set bs \<longrightarrow> square_free a \<and> degree a > 0)
  \<and> (\<forall> a i b j. (a,i) \<in> set bs \<longrightarrow> (b,j) \<in> set bs \<longrightarrow> (a,i) \<noteq> (b,j) \<longrightarrow> coprime a b)
  \<and> distinct bs"

lemma square_free_factorizationD: assumes "square_free_factorization p (c,bs)"
  shows "p = smult c (\<Prod>(a, i)\<in> set bs. a ^ Suc i)"
  "(a,i) \<in> set bs \<Longrightarrow> square_free a \<and> degree a \<noteq> 0"
  "(a,i) \<in> set bs \<Longrightarrow> (b,j) \<in> set bs \<Longrightarrow> (a,i) \<noteq> (b,j) \<Longrightarrow> coprime a b"
  "p = 0 \<Longrightarrow> c = 0 \<and> bs = []"
  "distinct bs"
  using assms unfolding square_free_factorization_def split by blast+

lemma square_free_factorization_prod_list: assumes "square_free_factorization p (c,bs)"
  shows "p = smult c (prod_list (map (\<lambda> (a,i). a ^ Suc i) bs))"
proof -
  note sff = square_free_factorizationD[OF assms]
  show ?thesis unfolding sff(1) 
    by (simp add: prod.distinct_set_conv_list[OF sff(5)])
qed
end

subsection \<open>Yun's factorization algorithm\<close>
locale yun_gcd = 
  fixes Gcd :: "'a :: factorial_ring_gcd poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
begin

partial_function (tailrec) yun_factorization_main :: 
  "'a poly \<Rightarrow> 'a poly \<Rightarrow>
    nat \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  [code]: "yun_factorization_main bn cn i sqr = (
    if bn = 1 then sqr
    else (
    let 
      dn = cn - pderiv bn;
      an = Gcd bn dn
    in yun_factorization_main (bn div an) (dn div an) (Suc i) ((an,i) # sqr)))"

definition yun_monic_factorization :: "'a poly \<Rightarrow> ('a poly \<times> nat)list" where
  "yun_monic_factorization p = (let
    pp = pderiv p;
    u = Gcd p pp;
    b0 = p div u;
    c0 = pp div u
    in 
      (filter (\<lambda> (a,i). a \<noteq> 1) (yun_factorization_main b0 c0 0 [])))"

definition square_free_monic_poly :: "'a poly \<Rightarrow> 'a poly" where
  "square_free_monic_poly p = (p div (Gcd p (pderiv p)))"
end

declare yun_gcd.yun_monic_factorization_def [code] 
declare yun_gcd.yun_factorization_main.simps [code] 
declare yun_gcd.square_free_monic_poly_def [code]

context 
  fixes Gcd :: "'a :: {field_char_0,euclidean_ring_gcd} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
begin
interpretation yun_gcd Gcd .

definition square_free_poly :: "'a poly \<Rightarrow> 'a poly" where
  "square_free_poly p = (if p = 0 then 0 else 
     square_free_monic_poly (smult (inverse (coeff p (degree p))) p))"


definition yun_factorization :: "'a poly \<Rightarrow> 'a \<times> ('a poly \<times> nat)list" where
  "yun_factorization p = (if p = 0
    then (0,[]) else (let 
      c = coeff p (degree p);
      q = smult (inverse c) p
    in (c, yun_monic_factorization q)))"

lemma yun_factorization_0[simp]: "yun_factorization 0 = (0,[])"
  unfolding yun_factorization_def by simp
end

locale monic_factorization =
  fixes as :: "('a :: {field_char_0,euclidean_ring_gcd} poly \<times> nat) set"
  and p :: "'a poly"
  assumes p: "p = prod (\<lambda> (a,i). a ^ Suc i) as"
  and fin: "finite as"
  assumes as_distinct: "\<And> a i b j. (a,i) \<in> as \<Longrightarrow> (b,j) \<in> as \<Longrightarrow> (a,i) \<noteq> (b,j) \<Longrightarrow> a \<noteq> b"
  and as_irred: "\<And> a i. (a,i) \<in> as \<Longrightarrow> irreducible\<^sub>d a"
  and as_monic: "\<And> a i. (a,i) \<in> as \<Longrightarrow> monic a"
begin

lemma poly_exp_expand: 
  "p = (prod (\<lambda> (a,i). a ^ i) as) * prod (\<lambda> (a,i). a) as"
  unfolding p prod.distrib[symmetric]
  by (rule prod.cong, auto)

lemma pderiv_exp_prod: 
  "pderiv p = (prod (\<lambda> (a,i). a ^ i) as * sum (\<lambda> (a,i). 
    prod (\<lambda> (b,j). b) (as - {(a,i)}) * smult (of_nat (Suc i)) (pderiv a)) as)"
  unfolding p pderiv_prod sum_distrib_left
proof (rule sum.cong[OF refl])
  fix x
  assume "x \<in> as"
  then obtain a i where x: "x = (a,i)" and mem: "(a,i) \<in> as" by (cases x, auto)
  let ?si = "smult (of_nat (Suc i)) :: 'a poly \<Rightarrow> 'a poly"
  show "(\<Prod>(a, i)\<in>as - {x}. a ^ Suc i) * pderiv (case x of (a, i) \<Rightarrow> a ^ Suc i) =
         (\<Prod>(a, i)\<in>as. a ^ i) *
         (case x of (a, i) \<Rightarrow> (\<Prod>(a, i)\<in>as - {(a, i)}. a) * smult (of_nat (Suc i)) (pderiv a))"
    unfolding x split pderiv_power_Suc
  proof -
    let ?prod = "\<Prod>(a, i)\<in>as - {(a, i)}. a ^ Suc i"
    let ?l = "?prod * (?si (a ^ i) * pderiv a)"
    let ?r = "(\<Prod>(a, i)\<in>as. a ^ i) * ((\<Prod>(a, i)\<in>as - {(a, i)}. a) * ?si (pderiv a))"
    have "?r = a ^ i * ((\<Prod>(a, i)\<in>as - {(a, i)}. a ^ i) * (\<Prod>(a, i)\<in>as - {(a, i)}. a) * ?si (pderiv a))"
      unfolding prod.remove[OF fin mem] by (simp add: ac_simps)
    also have "(\<Prod>(a, i)\<in>as - {(a, i)}. a ^ i) * (\<Prod>(a, i)\<in>as - {(a, i)}. a) 
      = ?prod" unfolding prod.distrib[symmetric]
      by (rule prod.cong[OF refl], auto)
    finally show "?l = ?r"
      by (simp add: ac_simps)
  qed
qed

lemma monic_gen: assumes "bs \<subseteq> as"
  shows "monic (\<Prod> (a, i) \<in> bs. a)"
  by (rule monic_prod, insert assms as_monic, auto)

lemma nonzero_gen: assumes "bs \<subseteq> as"
  shows "(\<Prod> (a, i) \<in> bs. a) \<noteq> 0"
  using monic_gen[OF assms] by auto

lemma monic_Prod: "monic ((\<Prod>(a, i)\<in>as. a ^ i))"
  by (rule monic_prod, insert as_monic, auto intro: monic_power)

lemma coprime_generic: 
  assumes bs: "bs \<subseteq> as"
  and f: "\<And> a i. (a,i) \<in> bs \<Longrightarrow> f i > 0"
  shows "coprime (\<Prod>(a, i) \<in> bs. a)
     (\<Sum>(a, i)\<in> bs. (\<Prod>(b, j)\<in> bs - {(a, i)} . b) * smult (of_nat (f i)) (pderiv a))"
  (is "coprime ?single ?onederiv")
proof -
  have single: "?single \<noteq> 0" by (rule nonzero_gen[OF bs])
  show ?thesis
  proof (rule gcd_eq_1_imp_coprime, rule gcdI [symmetric])
    fix k
    assume dvd: "k dvd ?single" "k dvd ?onederiv"
    note bs_monic = as_monic[OF subsetD[OF bs]]
    from dvd(1) single have k: "k \<noteq> 0" by auto
    show "k dvd 1"
    proof (cases "degree k > 0")
      case False
      with k obtain c where "k = [:c:]"
        by (auto dest: degree0_coeffs)
      with k have "c \<noteq> 0"
        by auto
      with \<open>k = [:c:]\<close> show "is_unit k"
        using dvdI [of 1 "[:c:]" "[:1 / c:]"] by auto
    next
      case True
      from irreducible\<^sub>d_factor[OF this]
      obtain p q where k: "k = p * q" and p: "irreducible p" by auto
      from k dvd have dvd: "p dvd ?single" "p dvd ?onederiv" unfolding dvd_def by auto
      from irreducible_dvd_prod[OF p dvd(1)] obtain a i where ai: "(a,i) \<in> bs" and pa: "p dvd a"
        by force
      then obtain q where a: "a = p * q" unfolding dvd_def by auto
      from p[unfolded irreducible\<^sub>d_def] have p0: "degree p > 0" by auto
      from irreducible\<^sub>d_dvd_smult[OF p0 as_irred pa] ai bs
        obtain c where c: "c \<noteq> 0" and ap: "a = smult c p" by auto
      hence ap': "p = smult (1/c) a" by auto
      let ?prod = "\<lambda> a i. (\<Prod>(b, j)\<in>bs - {(a, i)}. b) * smult (of_nat (f i)) (pderiv a)"
      let ?prod' = "\<lambda> aa ii a i. (\<Prod>(b, j)\<in>bs - {(a, i),(aa,ii)}. b) * smult (of_nat (f i)) (pderiv a)"
      define factor where "factor = sum (\<lambda> (b,j). ?prod' a i b j ) (bs - {(a,i)})"
      define fac where "fac = q * factor"
      from fin finite_subset[OF bs] have fin: "finite bs" by auto
      have "?onederiv = ?prod a i + sum (\<lambda> (b,j). ?prod b j) (bs - {(a,i)})"
        by (subst sum.remove[OF fin ai], auto)
      also have "sum (\<lambda> (b,j). ?prod b j) (bs - {(a,i)})
        = a * factor"
        unfolding factor_def sum_distrib_left
      proof (rule sum.cong[OF refl])
        fix bj
        assume mem: "bj \<in> bs - {(a,i)}"
        obtain b j where bj: "bj = (b,j)" by force
        from mem bj ai have ai: "(a,i) \<in> bs - {(b,j)}" by auto
        have id: "bs - {(b, j)} - {(a, i)} = bs - {(b,j),(a,i)}" by auto
        show "(\<lambda> (b,j). ?prod b j) bj = a * (\<lambda> (b,j). ?prod' a i b j) bj"
          unfolding bj split
          by (subst prod.remove[OF _ ai], insert fin, auto simp: id ac_simps)
      qed
      finally have "?onederiv = ?prod a i + p * fac" unfolding fac_def a by simp
      from dvd(2)[unfolded this] have "p dvd ?prod a i" by algebra
      from this[unfolded field_poly_irreducible_dvd_mult[OF p]]
      have False
      proof
        assume "p dvd (\<Prod>(b, j)\<in>bs - {(a, i)}. b)" 
        from irreducible_dvd_prod[OF p this] obtain b j where bj': "(b,j) \<in> bs - {(a,i)}"
          and pb: "p dvd b" by auto
        hence bj: "(b,j) \<in> bs" by auto
        from as_irred bj bs have "irreducible\<^sub>d b" by auto
        from irreducible\<^sub>d_dvd_smult[OF p0 this pb] obtain d where d: "d \<noteq> 0" 
          and b: "b = smult d p" by auto
        with ap c have id: "smult (c/d) b = a" and deg: "degree a = degree b" by auto
        from coeff_smult[of "c/d" b "degree b", unfolded id] deg bs_monic[OF ai] bs_monic[OF bj]
        have "c / d = 1" by simp
        from id[unfolded this] have "a = b" by simp
        with as_distinct[OF subsetD[OF bs ai] subsetD[OF bs bj]] bj'
        show False by auto
      next
        from f[OF ai] obtain k where fi: "f i = Suc k" by (cases "f i", auto)
        assume "p dvd smult (of_nat (f i)) (pderiv a)"
        hence "p dvd (pderiv a)" unfolding fi using dvd_smult_cancel of_nat_eq_0_iff by blast
        from this[unfolded ap] have "p dvd pderiv p" using c
          by (metis \<open>p dvd pderiv a\<close> ap' dvd_trans dvd_triv_right mult.left_neutral pderiv_smult smult_dvd_cancel)
        with not_dvd_pderiv p0 show False by auto
      qed
      thus "k dvd 1" by simp
    qed
  qed (insert \<open>?single \<noteq> 0\<close>, auto)
qed

lemma pderiv_exp_gcd: 
  "gcd p (pderiv p) = (\<Prod>(a, i)\<in>as. a ^ i)" (is "_ = ?prod")
proof -
  let ?sum = "(\<Sum>(a, i)\<in>as. (\<Prod>(b, j)\<in>as - {(a, i)}. b) * smult (of_nat (Suc i)) (pderiv a))"
  let ?single = "(\<Prod>(a, i)\<in>as. a)"
  let ?prd = "\<lambda> a i. (\<Prod>(b, j)\<in>as - {(a, i)}. b) * smult (of_nat (Suc i)) (pderiv a)"
  let ?onederiv = "\<Sum>(a, i)\<in>as. ?prd a i"
  have pp: "pderiv p = ?prod * ?sum" by (rule pderiv_exp_prod)
  have p: "p = ?prod * ?single" by (rule poly_exp_expand)
  have monic: "monic ?prod" by (rule monic_Prod)
  have gcd: "coprime ?single ?onederiv" 
    by (rule coprime_generic, auto)
  then have gcd: "gcd ?single ?onederiv = 1"
    by simp
  show ?thesis unfolding pp unfolding p poly_gcd_monic_factor [OF monic] gcd by simp
qed

lemma p_div_gcd_p_pderiv: "p div (gcd p (pderiv p)) = (\<Prod>(a, i)\<in>as. a)"
  unfolding pderiv_exp_gcd unfolding poly_exp_expand
  by (rule nonzero_mult_div_cancel_left, insert monic_Prod, auto)

fun A B C D :: "nat \<Rightarrow> 'a poly" where
  "A n = gcd (B n) (D n)"
| "B 0 = p div (gcd p (pderiv p))"
| "B (Suc n) = B n div A n"
| "C 0 = pderiv p div (gcd p (pderiv p))"
| "C (Suc n) = D n div A n"
| "D n = C n - pderiv (B n)"

lemma A_B_C_D: "A n = (\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a)"
  "B n = (\<Prod> (a, i) \<in> as - UNIV \<times> {0 ..< n}. a)"
  "C n = (\<Sum>(a, i)\<in>as - UNIV \<times> {0 ..< n}. 
    (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * smult (of_nat (Suc i - n)) (pderiv a))"
  "D n = (\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a) * 
    (\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< Suc n}. 
      (\<Prod>(b, j)\<in> as - UNIV \<times> {0 ..< Suc n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a)))"
proof (induct n and n and n and n rule: A_B_C_D.induct)
  case (1 n) (* A *)
  note Bn = 1(1)
  note Dn = 1(2)
  have "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..< n}. a) = (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) * (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a)"
    by (subst prod.union_disjoint[symmetric], auto, insert fin, auto intro: prod.cong)
  note Bn' = Bn[unfolded this]
  let ?an = "(\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a)"
  let ?bn = "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a)"
  show "A n = ?an" unfolding A.simps
  proof (rule gcdI[symmetric, OF _ _ _ normalize_monic[OF monic_gen]])
    have monB1: "monic (B n)" unfolding Bn by (rule monic_gen, auto)
    hence "B n \<noteq> 0" by auto
    let ?dn = "(\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< Suc n}. 
        (\<Prod>(b, j)\<in> as - UNIV \<times> {0 ..< Suc n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a)))"
    have Dn: "D n = ?an * ?dn" unfolding Dn by auto
    show dvd1: "?an dvd B n" unfolding Bn' dvd_def by blast
    show dvd2: "?an dvd D n" unfolding Dn dvd_def by blast
    {
      fix k
      assume "k dvd B n" "k dvd D n"
      from dvd_gcd_mult[OF this[unfolded Bn' Dn]]
      have "k dvd ?an * (gcd ?bn ?dn)" .
      moreover have "coprime ?bn ?dn"
        by (rule coprime_generic, auto)
      ultimately show "k dvd ?an" by simp
    }
  qed auto
next
  case 2 (* B 0 *)
  have as: "as - UNIV \<times> {0..<0} = as" by auto
  show ?case unfolding B.simps as p_div_gcd_p_pderiv by auto
next
  case (3 n) (* B n *)
  have id: "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..< n}. a) = (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a) * (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a)"
    by (subst prod.union_disjoint[symmetric], auto, insert fin, auto intro: prod.cong)
  show ?case unfolding B.simps 3 id
    by (subst nonzero_mult_div_cancel_right[OF nonzero_gen], auto)
next
  case 4 (* C 0 *)
  have as: "as - UNIV \<times> {0..<0} = as" "\<And> i. Suc i - 0 = Suc i" by auto
  show ?case unfolding C.simps pderiv_exp_gcd unfolding pderiv_exp_prod as
    by (rule nonzero_mult_div_cancel_left, insert monic_Prod, auto)
next
  case (5 n) (* C n *)
  show ?case unfolding C.simps 5
    by (subst nonzero_mult_div_cancel_left, rule nonzero_gen, auto)
next
  case (6 n) (* D n *)
  let ?f = "\<lambda> (a,i). (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a))"
  have "D n = (\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< n}. (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * 
    (smult (of_nat (Suc i - n)) (pderiv a) - pderiv a))"
    unfolding D.simps 6 pderiv_prod sum_subtractf[symmetric] right_diff_distrib
    by (rule sum.cong, auto)
  also have "\<dots> = sum ?f (as - UNIV \<times> {0 ..< n})"
  proof (rule sum.cong[OF refl])
    fix x
    assume "x \<in> as - UNIV \<times> {0 ..< n}"
    then obtain a i where x: "x = (a,i)" and i: "Suc i > n" by (cases x, auto)
    hence id: "Suc i - n = Suc (i - n)" by arith
    have id: "of_nat (Suc i - n) = of_nat (i - n) + (1 :: 'a)" unfolding id by simp
    have id: "smult (of_nat (Suc i - n)) (pderiv a) - pderiv a = smult (of_nat (i - n)) (pderiv a)" 
      unfolding id smult_add_left by auto
    have cong: "\<And> x y z :: 'a poly. x = y \<Longrightarrow> x * z = y * z" by auto
    show "(case x of
          (a, i) \<Rightarrow>
            (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) *
            (smult (of_nat (Suc i - n)) (pderiv a) - pderiv a)) =
         (case x of
          (a, i) \<Rightarrow> (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a))"
      unfolding x split id
      by (rule cong, auto)
  qed
  also have "\<dots> = sum ?f (as - UNIV \<times> {0 ..< Suc n}) + sum ?f (as \<inter> UNIV \<times> {n})"
    by (subst sum.union_disjoint[symmetric], insert fin, auto intro: sum.cong)
  also have "sum ?f (as \<inter> UNIV \<times> {n}) = 0"
    by (rule sum.neutral, auto)
  finally have id: "D n = sum ?f (as - UNIV \<times> {0 ..< Suc n})" by simp
  show ?case unfolding id sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix x
    assume mem: "x \<in> as - UNIV \<times> {0 ..< Suc n}"
    obtain a i where x: "x = (a,i)" by force
    with mem have i: "i > n" by auto
    have cong: "\<And> x y z v :: 'a poly. x = y * v \<Longrightarrow> x * z = y * (v * z)" by auto
    show "(case x of
          (a, i) \<Rightarrow> (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a)) =
         (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) *
         (case x of (a, i) \<Rightarrow>
            (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<Suc n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a))"
      unfolding x split
      by (rule cong, subst prod.union_disjoint[symmetric], insert fin, (auto)[3],
        rule prod.cong, insert i, auto) 
  qed
qed

lemmas A = A_B_C_D(1)
lemmas B = A_B_C_D(2)

lemmas ABCD_simps = A.simps B.simps C.simps D.simps
declare ABCD_simps[simp del]

lemma prod_A: 
  "(\<Prod>i = 0..< n. A i ^ Suc i) = (\<Prod>(a, i)\<in> as \<inter> UNIV \<times> {0 ..< n}. a ^ Suc i)"
proof (induct n)
  case (Suc n)
  have id: "{0 ..< Suc n} = insert n {0 ..< n}" by auto
  have id2: "as \<inter> UNIV \<times> {0 ..< Suc n} = as \<inter> UNIV \<times> {n} \<union> as \<inter> UNIV \<times> {0 ..< n}" by auto
  have cong: "\<And> x y z. x = y \<Longrightarrow> x * z = y * z" by auto
  show ?case unfolding id2 unfolding id 
  proof (subst prod.insert; (subst prod.union_disjoint)?; (unfold Suc)?; 
    (unfold A, rule cong)?)
    show "(\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) ^ Suc n = (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a ^ Suc i)"
      unfolding prod_power_distrib
      by (rule prod.cong, auto)
  qed (insert fin, auto)
qed simp

lemma prod_A_is_p_unknown: assumes "\<And> a i. (a,i) \<in> as \<Longrightarrow> i < n"
  shows "p = (\<Prod>i = 0..< n. A i ^ Suc i)"
proof -
  have "p = (\<Prod>(a, i)\<in>as. a ^ Suc i)" by (rule p)
  also have "\<dots> = (\<Prod>i = 0..< n. A i ^ Suc i)" unfolding prod_A
    by (rule prod.cong, insert assms, auto)
  finally show ?thesis .
qed

definition bound :: nat where
  "bound = Suc (Max (snd ` as))"

lemma bound: assumes m: "m \<ge> bound"
  shows "B m = 1"
proof -
  let ?set = "as - UNIV \<times> {0..<m}"
  {
    fix a i
    assume ai: "(a,i) \<in> ?set"
    hence "i \<in> snd ` as" by force
    from Max_ge[OF _ this] fin have "i \<le> Max (snd ` as)" by auto
    with ai m[unfolded bound_def] have False by auto
  }
  hence id: "?set = {}" by force
  show "B m = 1" unfolding B id by simp
qed

lemma coprime_A_A: assumes "i \<noteq> j"
  shows "coprime (A i) (A j)"
proof (rule coprimeI)
  fix k  
  assume dvd: "k dvd A i" "k dvd A j"
  have Ai: "A i \<noteq> 0" unfolding A
    by (rule nonzero_gen, auto)
  with dvd have k: "k \<noteq> 0" by auto
  show "is_unit k"
  proof (cases "degree k > 0")
    case False
    then obtain c where kc: "k = [: c :]" by (auto dest: degree0_coeffs)
    with k have "1 = k * [:1 / c:]"
      by simp
    thus ?thesis unfolding dvd_def by blast
  next
    case True
    from irreducible_monic_factor[OF this]
    obtain q r where k: "k = q * r" and q: "irreducible q" and mq: "monic q" by auto
    with dvd have dvd: "q dvd A i" "q dvd A j" unfolding dvd_def by auto
    from q have q0: "degree q > 0" unfolding irreducible\<^sub>d_def by auto
    from irreducible_dvd_prod[OF q dvd(1)[unfolded A]]
      obtain a where ai: "(a,i) \<in> as" and qa: "q dvd a" by auto
    from irreducible_dvd_prod[OF q dvd(2)[unfolded A]]
      obtain b where bj: "(b,j) \<in> as" and qb: "q dvd b" by auto
    from as_distinct[OF ai bj] assms have neq: "a \<noteq> b" by auto
    from irreducible\<^sub>d_dvd_smult[OF q0 as_irred[OF ai] qa]
      irreducible\<^sub>d_dvd_smult[OF q0 as_irred[OF bj] qb]
    obtain c d where "c \<noteq> 0" "d \<noteq> 0" "a = smult c q" "b = smult d q" by auto
    hence ab: "a = smult (c / d) b" and "c / d \<noteq> 0" by auto
    with as_monic[OF bj] as_monic[OF ai] arg_cong[OF ab, of "\<lambda> p. coeff p (degree p)"] 
    have "a = b" unfolding coeff_smult degree_smult_eq by auto
    with neq show ?thesis by auto
  qed
qed

lemma A_monic: "monic (A i)"
  unfolding A by (rule monic_gen, auto)

lemma A_square_free: "square_free (A i)"
proof (rule square_freeI)
  fix q k
  have mon: "monic (A i)" by (rule A_monic)
  hence Ai: "A i \<noteq> 0" by auto
  assume q: "degree q > 0" and dvd: "q * q dvd A i"
  from irreducible_monic_factor[OF q] obtain r s where q: "q = r * s" and 
    irr: "irreducible r" and mr: "monic r" by auto
  from dvd[unfolded q] have dvd2: "r * r dvd A i" and dvd1: "r dvd A i" unfolding dvd_def by auto
  from irreducible_dvd_prod[OF irr dvd1[unfolded A]] 
    obtain a where ai: "(a,i) \<in> as" and ra: "r dvd a" by auto
  let ?rem = "(\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {i} - {(a,i)}. a)"
  have a: "irreducible\<^sub>d a" by (rule as_irred[OF ai])
  from irreducible\<^sub>d_dvd_smult[OF _ a ra] irr
    obtain c where ar: "a = smult c r"  and "c \<noteq> 0" by force
  with mr as_monic[OF ai] arg_cong[OF ar, of "\<lambda> p. coeff p (degree p)"] 
  have "a = r" unfolding coeff_smult degree_smult_eq by auto 
  with dvd2 have dvd: "a * a dvd A i" by simp
  have id: "A i = a * ?rem" unfolding A
    by (subst prod.remove[of _ "(a,i)"], insert ai fin, auto)
  with dvd have "a dvd ?rem" using a id Ai by auto
  from irreducible_dvd_prod[OF _ this] a obtain b where bi: "(b,i) \<in> as" 
    and neq: "b \<noteq> a" and ab: "a dvd b" by auto
  from as_irred[OF bi] have b: "irreducible\<^sub>d b" . 
  from irreducible\<^sub>d_dvd_smult[OF _ b ab] a[unfolded irreducible\<^sub>d_def]
  obtain c where "c \<noteq> 0" and ba: "b = smult c a" by auto
  with as_monic[OF bi] as_monic[OF ai] arg_cong[OF ba, of "\<lambda> p. coeff p (degree p)"] 
  have "a = b" unfolding coeff_smult degree_smult_eq by auto
  with neq show False by auto
qed (insert A_monic[of i], auto)


lemma prod_A_is_p_B_bound: assumes "B n = 1"
  shows "p = (\<Prod>i = 0..< n. A i ^ Suc i)"
proof (rule prod_A_is_p_unknown)
  fix a i
  assume ai: "(a,i) \<in> as"
  let ?rem = "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..<n} - {(a,i)}. a)"
  have rem: "?rem \<noteq> 0"
    by (rule nonzero_gen, auto)
  have "irreducible\<^sub>d a" using as_irred[OF ai] .
  hence a: "a \<noteq> 0" "degree a \<noteq> 0" unfolding irreducible\<^sub>d_def by auto
  show "i < n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "i \<ge> n" by auto
    with ai have mem: "(a,i) \<in> as - UNIV \<times> {0 ..< n}" by auto
    have "0 = degree (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<n}. a)" using assms unfolding B by simp
    also have "\<dots> = degree (a * ?rem)"
      by (subst prod.remove[OF _ mem], insert fin, auto)
    also have "\<dots> = degree a + degree ?rem"
      by (rule degree_mult_eq[OF a(1) rem])
    finally show False using a(2) by auto
  qed
qed

interpretation yun_gcd gcd .

lemma square_free_monic_poly: "(poly (square_free_monic_poly p) x = 0) = (poly p x = 0)"
proof -
  show ?thesis unfolding square_free_monic_poly_def unfolding p_div_gcd_p_pderiv
    unfolding p poly_prod prod_zero_iff[OF fin] by force
qed

lemma yun_factorization_induct: assumes base: "\<And> bn cn. bn = 1 \<Longrightarrow> P bn cn"
  and step: "\<And> bn cn. bn \<noteq> 1 \<Longrightarrow> P (bn div (gcd bn (cn - pderiv bn))) 
    ((cn - pderiv bn) div (gcd bn (cn - pderiv bn))) \<Longrightarrow> P bn cn"
  and id: "bn = p div gcd p (pderiv p)" "cn = pderiv p div gcd p (pderiv p)"
  shows "P bn cn"
proof -
  define n where "n = (0 :: nat)"
  let ?m = "\<lambda> n. bound - n"
  have "P (B n) (C n)"
  proof (induct n rule: wf_induct[OF wf_measure[of ?m]])
    case (1 n)
    note IH = 1(1)[rule_format]
    show ?case
    proof (cases "B n = 1")
      case True
      with base show ?thesis by auto
    next
      case False note Bn = this
      with bound[of n] have "\<not> bound \<le> n" by auto
      hence "(Suc n, n) \<in> measure ?m" by auto
      note IH = IH[OF this]
      show ?thesis
        by (rule step[OF Bn], insert IH, simp add: D.simps C.simps B.simps A.simps)
    qed
  qed
  thus ?thesis unfolding id n_def B.simps C.simps .
qed

lemma yun_factorization_main: assumes "yun_factorization_main (B n) (C n) n bs = cs"
  "set bs = {(A i, i) | i. i < n}" "distinct (map snd bs)"
  shows "\<exists> m. set cs = {(A i, i) | i. i < m} \<and> B m = 1 \<and> distinct (map snd cs)"
  using assms
proof -
  let ?m = "\<lambda> n. bound - n"
  show ?thesis using assms 
  proof (induct n arbitrary: bs rule: wf_induct[OF wf_measure[of ?m]])
    case (1 n)
    note IH = 1(1)[rule_format]
    have res: "yun_factorization_main (B n) (C n) n bs = cs" by fact
    note res = res[unfolded yun_factorization_main.simps[of "B n"]]
    have bs: "set bs = {(A i, i) |i. i < n}" "distinct (map snd bs)" by fact+
    show ?case
    proof (cases "B n = 1")
      case True
      with res have "bs = cs" by auto
      with True bs show ?thesis by auto
    next
      case False note Bn = this
      with bound[of n] have "\<not> bound \<le> n" by auto
      hence "(Suc n, n) \<in> measure ?m" by auto
      note IH = IH[OF this]
      from Bn res[unfolded Let_def, folded D.simps C.simps B.simps A.simps] 
      have res: "yun_factorization_main (B (Suc n)) (C (Suc n)) (Suc n) ((A n, n) # bs) = cs"
        by simp
      note IH = IH[OF this]
      {
        fix i 
        assume "i < Suc n" "\<not> i < n"
        hence "n = i" by arith
      } note missing = this
      have "set ((A n, n) # bs) = {(A i, i) |i. i < Suc n}"
        unfolding list.simps bs by (auto, subst missing, auto)
      note IH = IH[OF this]
      from bs have "distinct (map snd ((A n, n) # bs))" by auto
      note IH = IH[OF this]
      show ?thesis by (rule IH)
    qed
  qed
qed

lemma yun_monic_factorization_res: assumes res: "yun_monic_factorization p = bs"
  shows "\<exists> m. set bs = {(A i, i) | i. i < m \<and> A i \<noteq> 1} \<and> B m = 1 \<and> distinct (map snd bs)"
proof -
  from res[unfolded yun_monic_factorization_def Let_def, 
    folded B.simps C.simps]
  obtain cs where yun: "yun_factorization_main (B 0) (C 0) 0 [] = cs" and bs: "bs = filter (\<lambda> (a,i). a \<noteq> 1) cs" 
    by auto
  from yun_factorization_main[OF yun] show ?thesis unfolding bs
    by (auto simp: distinct_map_filter)
qed                                                    

lemma yun_monic_factorization: assumes yun: "yun_monic_factorization p = bs"
  shows "square_free_factorization p (1,bs)" "(b,i) \<in> set bs \<Longrightarrow> monic b" "distinct (map snd bs)" 
proof -
  from yun_monic_factorization_res[OF yun]
  obtain m where bs: "set bs = {(A i, i) | i. i < m \<and> A i \<noteq> 1}" and B: "B m = 1" 
    and dist: "distinct (map snd bs)" by auto
  have id: "{0 ..< m} = {i. i < m \<and> A i = 1} \<union> {i. i < m \<and> A i \<noteq> 1}" (is "_ = ?ignore \<union> _") by auto
  have "p = (\<Prod>i = 0..<m. A i ^ Suc i)"
    by (rule prod_A_is_p_B_bound[OF B])
  also have "\<dots> = prod (\<lambda> i. A i ^ Suc i) {i. i < m \<and> A i \<noteq> 1}"
    unfolding id 
    by (subst prod.union_disjoint, (force+)[3],
    subst prod.neutral[of ?ignore], auto)
  also have "\<dots> = (\<Prod>(a, i)\<in> set bs. a ^ Suc i)" unfolding bs
    by (rule prod.reindex_cong[of snd], auto simp: inj_on_def, force)
  finally have 1: "p = (\<Prod>(a, i)\<in> set bs. a ^ Suc i)" .
  {
    fix a i
    assume "(a,i) \<in> set bs"
    hence A: "a = A i" "A i \<noteq> 1" unfolding bs by auto
    with A_square_free[of i] A_monic[of i] have "square_free a \<and> degree a \<noteq> 0" "monic a"
      by (auto simp: monic_degree_0)
  } note 2 = this
  {
    fix a i b j
    assume ai: "(a,i) \<in> set bs" and bj: "(b,j) \<in> set bs" and neq: "(a,i) \<noteq> (b,j)"
    hence a: "a = A i" and b: "b = A j" unfolding bs by auto
    from neq dist ai bj have neq: "i \<noteq> j" using a b by blast
    from coprime_A_A [OF neq] have "coprime a b" unfolding a b .
  } note 3 = this
  have "monic p" unfolding p 
    by (rule monic_prod, insert as_monic, auto intro: monic_power monic_mult)
  hence 4: "p \<noteq> 0" by auto
  from dist have 5: "distinct bs" unfolding distinct_map ..
  show "square_free_factorization p (1,bs)"
    unfolding square_free_factorization_def using 1 2 3 4 5
    by auto
  show "(b,i) \<in> set bs \<Longrightarrow> monic b" using 2 by auto
  show "distinct (map snd bs)" by fact
qed
end

lemma monic_factorization: assumes "monic p"
  shows "\<exists> as. monic_factorization as p"
proof -
  from monic_irreducible_factorization[OF assms]
  obtain as f where fin: "finite as" and p: "p = (\<Prod>a\<in>as. a ^ Suc (f a))" 
    and as: "as \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    by auto
  define cs where "cs = {(a, f a) | a. a \<in> as}"
  show ?thesis
  proof (rule exI, standard)  
    show "finite cs" unfolding cs_def using fin by auto
    {
      fix a i
      assume "(a,i) \<in> cs"
      thus "irreducible\<^sub>d a" "monic a" unfolding cs_def using as by auto
    } note irr = this
    show "\<And>a i b j. (a, i) \<in> cs \<Longrightarrow> (b, j) \<in> cs \<Longrightarrow> (a, i) \<noteq> (b, j) \<Longrightarrow> a \<noteq> b" unfolding cs_def by auto
    show "p = (\<Prod>(a, i)\<in>cs. a ^ Suc i)" unfolding p cs_def
      by (rule prod.reindex_cong, auto, auto simp: inj_on_def)
  qed
qed

lemma square_free_monic_poly: assumes "monic (p :: 'a :: {field_char_0, euclidean_ring_gcd} poly)"
  shows "(poly (yun_gcd.square_free_monic_poly gcd p) x = 0) = (poly p x = 0)"
proof -
  from monic_factorization[OF assms] obtain as where "monic_factorization as p" ..
  from monic_factorization.square_free_monic_poly[OF this] show ?thesis .
qed

lemma yun_factorization_induct: assumes base: "\<And> bn cn. bn = 1 \<Longrightarrow> P bn cn"
  and step: "\<And> bn cn. bn \<noteq> 1 \<Longrightarrow> P (bn div (gcd bn (cn - pderiv bn))) 
    ((cn - pderiv bn) div (gcd bn (cn - pderiv bn))) \<Longrightarrow> P bn cn"
  and id: "bn = p div gcd p (pderiv p)" "cn = pderiv p div gcd p (pderiv p)"
  and monic: "monic (p :: 'a :: {field_char_0,euclidean_ring_gcd} poly)"
  shows "P bn cn"
proof -
  from monic_factorization[OF monic] obtain as where "monic_factorization as p" ..
  from monic_factorization.yun_factorization_induct[OF this base step id] show ?thesis .
qed

lemma square_free_poly: 
  "(poly (square_free_poly gcd p) x = 0) = (poly p x = 0)"
proof (cases "p = 0")
  case True
  thus ?thesis unfolding square_free_poly_def by auto
next
  case False
  let ?c = "coeff p (degree p)"
  let ?ic = "inverse ?c"
  have id: "square_free_poly gcd p = yun_gcd.square_free_monic_poly gcd (smult ?ic p)"
    unfolding square_free_poly_def using False by auto
  from False have mon: "monic (smult ?ic p)" and ic: "?ic \<noteq> 0" by auto
  show ?thesis unfolding id square_free_monic_poly[OF mon]
    using ic by simp
qed  


lemma yun_monic_factorization: fixes p :: "'a :: {field_char_0,euclidean_ring_gcd} poly" 
  assumes res: "yun_gcd.yun_monic_factorization gcd p = bs"
  and monic: "monic p"
  shows "square_free_factorization p (1,bs)" "(b,i) \<in> set bs \<Longrightarrow> monic b" "distinct (map snd bs)" 
proof -
  from monic_factorization[OF monic] obtain as where "monic_factorization as p" ..
  from "monic_factorization.yun_monic_factorization"[OF this res]
  show "square_free_factorization p (1,bs)" "(b,i) \<in> set bs \<Longrightarrow> monic b" "distinct (map snd bs)" 
    by auto
qed

lemma square_free_factorization_smult: assumes c: "c \<noteq> 0"
  and sf: "square_free_factorization p (d,bs)"
  shows "square_free_factorization (smult c p) (c * d, bs)"
proof -
  from sf[unfolded square_free_factorization_def split]
  have p: "p = smult d (\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
    and eq: "p = 0 \<longrightarrow> d = 0 \<and> bs = []" by blast+
  from eq c have eq: "smult c p = 0 \<longrightarrow> c * d = 0 \<and> bs = []" by auto
  from p have p: "smult c p = smult (c * d) (\<Prod>(a, i)\<in>set bs. a ^ Suc i)" by auto
  from eq p sf show ?thesis unfolding square_free_factorization_def by blast
qed

lemma yun_factorization: assumes res: "yun_factorization gcd p = c_bs"
  shows "square_free_factorization p c_bs" "(b,i) \<in> set (snd c_bs) \<Longrightarrow> monic b"
proof -
  interpret yun_gcd gcd .
  note res = res[unfolded yun_factorization_def Let_def]
  have "square_free_factorization p c_bs \<and> ((b,i) \<in> set (snd c_bs) \<longrightarrow> monic b)"
  proof (cases "p = 0")
    case True
    with res have "c_bs = (0, [])" by auto    
    thus ?thesis unfolding True by (auto simp: square_free_factorization_def)
  next
    case False
    let ?c = "coeff p (degree p)"
    let ?ic = "inverse ?c"
    obtain c bs where cbs: "c_bs = (c,bs)" by force
    with False res
    have c: "c = ?c" "?c \<noteq> 0" and fact: "yun_monic_factorization (smult ?ic p) = bs" by auto
    from False have mon: "monic (smult ?ic p)" by auto
    from yun_monic_factorization[OF fact mon]
    have sff: "square_free_factorization (smult ?ic p) (1, bs)" "(b, i) \<in> set bs \<Longrightarrow> monic b" by auto
    have id: "smult ?c (smult ?ic p) = p" using False by auto
    from square_free_factorization_smult[OF c(2) sff(1), unfolded id] sff
    show ?thesis unfolding cbs c by simp
  qed
  thus "square_free_factorization p c_bs" "(b,i) \<in> set (snd c_bs) \<Longrightarrow> monic b" by blast+
qed


lemma prod_list_pow_suc: "(\<Prod>x\<leftarrow>bs. (x :: 'a :: comm_monoid_mult) * x ^ i) 
  = prod_list bs * prod_list bs ^ i" 
  by (induct bs, auto simp: field_simps)

declare irreducible_linear_field_poly[intro!]

context 
  assumes "SORT_CONSTRAINT('a :: {field, factorial_ring_gcd})" 
begin
lemma square_free_factorization_order_root_mem: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> (0 :: 'a poly)"
    and ai: "(a,i) \<in> set bs" and rt: "poly a x = 0"
  shows "order x p = Suc i"
proof -
  note sff = square_free_factorizationD[OF sff]
  let ?prod = "(\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
  from sff have pf: "p = smult c ?prod" by blast
  with p have c: "c \<noteq> 0" by auto
  have ord: "order x p = order x ?prod" unfolding pf 
    using order_smult[OF c] by auto
  define q where "q = [: -x, 1 :]"
  have q0: "q \<noteq> 0" unfolding q_def by auto
  have iq: "irreducible q" by (auto simp: q_def)
  from rt have qa: "q dvd a" unfolding q_def poly_eq_0_iff_dvd .
  then obtain b where aqb: "a = q * b" unfolding dvd_def by auto
  from sff(2)[OF ai] have sq: "square_free a" and mon: "degree a \<noteq> 0" by auto
  let ?rem = "(\<Prod>(a, i)\<in>set bs - {(a,i)}. a ^ Suc i)"
  have p0: "?prod \<noteq> 0" using p pf by auto
  have "?prod = a ^ Suc i * ?rem"
    by (subst prod.remove[OF _ ai], auto)
  also have "a ^ Suc i = q ^ Suc i * b ^ Suc i" unfolding aqb by (simp add: field_simps)
  finally have id: "?prod = q ^ Suc i * (b ^ Suc i * ?rem)" by simp
  hence dvd: "q ^ Suc i dvd ?prod" by auto
  {
    assume "q ^ Suc (Suc i) dvd ?prod"
    hence "q dvd ?prod div q ^ Suc i"
      by (metis dvd dvd_0_left_iff dvd_div_iff_mult p0 power_Suc)
    also have "?prod div q ^ Suc i = b ^ Suc i * ?rem"
      unfolding id by (rule nonzero_mult_div_cancel_left, insert q0, auto)
    finally have "q dvd b \<or> q dvd ?rem"
      using iq irreducible_dvd_pow[OF iq] by auto
    hence False
    proof
      assume "q dvd b"
      with aqb have "q * q dvd a" by auto
      with sq[unfolded square_free_def] mon iq show False
        unfolding irreducible\<^sub>d_def by auto
    next
      assume "q dvd ?rem"
      from irreducible_dvd_prod[OF iq this]
      obtain b j where bj: "(b,j) \<in> set bs" and neq: "(a,i) \<noteq> (b,j)" and dvd: "q dvd b ^ Suc j" by auto
      from irreducible_dvd_pow[OF iq dvd] have qb: "q dvd b" .
      from sff(3)[OF ai bj neq] have gcd: "coprime a b" .
      from qb qa have "q dvd gcd a b" by simp
      from dvd_imp_degree_le[OF this[unfolded gcd]] iq q0 show False
        using gcd by auto
    qed
  }
  hence ndvd: "\<not> q ^ Suc (Suc i) dvd ?prod" by blast
  with dvd have "order x ?prod = Suc i" unfolding q_def
    by (rule order_unique_lemma[symmetric])
  thus ?thesis unfolding ord .
qed

lemma square_free_factorization_order_root_no_mem: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> (0 :: 'a poly)"
    and no_root: "\<And> a i. (a,i) \<in> set bs \<Longrightarrow> poly a x \<noteq> 0"
  shows "order x p = 0"
proof (rule ccontr)
  assume o0: "order x p \<noteq> 0"
  with order_root[of p x] p have 0: "poly p x = 0" by auto
  note sff = square_free_factorizationD[OF sff]
  let ?prod = "(\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
  from sff have pf: "p = smult c ?prod" by blast
  with p have c: "c \<noteq> 0" by auto
  with 0 have 0: "poly ?prod x = 0" unfolding pf by auto
  define q where "q = [: -x, 1 :]"
  from 0 have dvd: "q dvd ?prod" unfolding poly_eq_0_iff_dvd by (simp add: q_def)  
  have q0: "q \<noteq> 0" unfolding q_def by auto
  have iq: "irreducible q" by (unfold q_def, auto intro:)
  from irreducible_dvd_prod[OF iq dvd]
  obtain a i where ai: "(a,i) \<in> set bs" and dvd: "q dvd a ^ Suc i" by auto
  from irreducible_dvd_pow[OF iq dvd] have dvd: "q dvd a" .
  hence "poly a x = 0" unfolding q_def by (simp add: poly_eq_0_iff_dvd q_def)
  with no_root[OF ai] show False by simp
qed

lemma square_free_factorization_order_root: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> (0 :: 'a poly)"
  shows "order x p = i \<longleftrightarrow> (i = 0 \<and> (\<forall> a j. (a,j) \<in> set bs \<longrightarrow> poly a x \<noteq> 0) 
    \<or> (\<exists> a j. (a,j) \<in> set bs \<and> poly a x = 0 \<and> i = Suc j))" (is "?l = (?r1 \<or> ?r2)")
proof -
  note mem = square_free_factorization_order_root_mem[OF sff p]
  note no_mem = square_free_factorization_order_root_no_mem[OF sff p]
  show ?thesis
  proof
    assume "?r1 \<or> ?r2"
    thus ?l
    proof
      assume ?r2
      then obtain a j where aj: "(a,j) \<in> set bs" "poly a x = 0" and i: "i = Suc j" by auto
      from mem[OF aj] i show ?l by simp
    next
      assume ?r1 
      with no_mem[of x] show ?l by auto
    qed
  next
    assume ?l
    show "?r1 \<or> ?r2"
    proof (cases "\<exists>a j. (a, j) \<in> set bs \<and> poly a x = 0")
      case True
      then obtain a j where "(a, j) \<in> set bs" "poly a x = 0" by auto
      with mem[OF this] \<open>?l\<close>
      have ?r2 by auto
      thus ?thesis ..
    next
      case False
      with no_mem[of x] \<open>?l\<close> have ?r1 by auto
      thus ?thesis ..
    qed
  qed
qed

lemma square_free_factorization_root: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> (0 :: 'a poly)"
  shows "{x. poly p x = 0} = {x. \<exists> a i. (a,i) \<in> set bs \<and> poly a x = 0}" 
  using square_free_factorization_order_root[OF sff p] p
  unfolding order_root by auto

lemma square_free_factorizationD': fixes p :: "'a poly"
  assumes sf: "square_free_factorization p (c, bs)"
  shows "p = smult c (\<Prod>(a, i) \<leftarrow> bs. a ^ Suc i)"
    and "square_free (prod_list (map fst bs))"
    and "\<And> b i. (b,i) \<in> set bs \<Longrightarrow> degree b \<noteq> 0"
    and "p = 0 \<Longrightarrow> c = 0 \<and> bs = []"
proof -
  note sf = square_free_factorizationD[OF sf]
  show "p = smult c (\<Prod>(a, i) \<leftarrow> bs. a ^ Suc i)" unfolding sf(1) using sf(5)
    by (simp add: prod.distinct_set_conv_list)
  show bs: "\<And> b i. (b,i) \<in> set bs \<Longrightarrow> degree b \<noteq> 0" using sf(2) by auto
  show "p = 0 \<Longrightarrow> c = 0 \<and> bs = []" using sf(4) .
  show "square_free (prod_list (map fst bs))"
  proof (rule square_freeI)
    from bs have "\<And> b. b \<in> set (map fst bs) \<Longrightarrow> b \<noteq> 0" by fastforce
    thus "prod_list (map fst bs) \<noteq> 0" unfolding prod_list_zero_iff by auto
    fix q
    assume "degree q > 0" "q * q dvd prod_list (map fst bs)"
    from irreducible\<^sub>d_factor[OF this(1)] this(2) obtain q where 
      irr: "irreducible q" and dvd: "q * q dvd prod_list (map fst bs)" unfolding dvd_def by auto
    hence dvd': "q dvd prod_list (map fst bs)" unfolding dvd_def by auto
    from irreducible_dvd_prod_list[OF irr dvd'] obtain b i where 
      mem: "(b,i) \<in> set bs" and dvd1: "q dvd b" by auto
    from dvd1 obtain k where b: "b = q * k" unfolding dvd_def by auto
    from split_list[OF mem] b obtain bs1 bs2 where bs: "bs = bs1 @ (b, i) # bs2" by auto
    from irr have q0: "q \<noteq> 0" and dq: "degree q > 0" unfolding irreducible\<^sub>d_def by auto
    from sf(2)[OF mem, unfolded b] have "square_free (q * k)" by auto
    from this[unfolded square_free_def, THEN conjunct2, rule_format, OF dq] 
    have qk: "\<not> q dvd k" by simp
    from dvd[unfolded bs b] have "q * q dvd q * (k * prod_list (map fst (bs1 @ bs2)))"
      by (auto simp: ac_simps)
    with q0 have "q dvd k * prod_list (map fst (bs1 @ bs2))" by auto
    with irr qk have "q dvd prod_list (map fst (bs1 @ bs2))" by auto
    from irreducible_dvd_prod_list[OF irr this] obtain b' i' where 
      mem': "(b',i') \<in> set (bs1 @ bs2)" and dvd2: "q dvd b'" by fastforce
    from dvd1 dvd2 have "q dvd gcd b b'" by auto
    with dq is_unit_iff_degree[OF q0] have cop: "\<not> coprime b b'" by force
    from mem' have "(b',i') \<in> set bs" unfolding bs by auto
    from sf(3)[OF mem this] cop have b': "(b',i') = (b,i)"
      by (auto simp add: coprime_iff_gcd_eq_1)
    with mem' sf(5)[unfolded bs] show False by auto
  qed
qed
  

lemma square_free_factorizationI': fixes p :: "'a poly"
  assumes prod: "p = smult c (\<Prod>(a, i) \<leftarrow> bs. a ^ Suc i)"
    and sf: "square_free (prod_list (map fst bs))"
    and deg: "\<And> b i. (b,i) \<in> set bs \<Longrightarrow> degree b > 0"
    and 0: "p = 0 \<Longrightarrow> c = 0 \<and> bs = []"
  shows "square_free_factorization p (c, bs)"
  unfolding square_free_factorization_def split
proof (intro conjI impI allI)
  show "p = 0 \<Longrightarrow> c = 0" "p = 0 \<Longrightarrow> bs = []" using 0 by auto
  {
    fix b i
    assume bi: "(b,i) \<in> set bs"
    from deg[OF this] show "degree b > 0" .
    have "b dvd prod_list (map fst bs)"
      by (intro prod_list_dvd, insert bi, force)
    from square_free_factor[OF this sf] show "square_free b" .
  }
  show dist: "distinct bs" 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from not_distinct_decomp[OF this] obtain bs1 bs2 bs3 b i where
      bs: "bs = bs1 @ [(b,i)] @ bs2 @ [(b,i)] @ bs3" by force
    hence "b * b dvd prod_list (map fst bs)" by auto
    with sf[unfolded square_free_def, THEN conjunct2, rule_format, of b] 
    have db: "degree b = 0" by auto
    from bs have "(b,i) \<in> set bs" by auto
    from deg[OF this] db show False by auto
  qed    
  show "p = smult c (\<Prod>(a, i)\<in>set bs. a ^ Suc i)" unfolding prod using dist 
    by (simp add: prod.distinct_set_conv_list)
  {
    fix a i b j
    assume ai: "(a, i) \<in> set bs" and bj: "(b, j) \<in> set bs" and diff: "(a, i) \<noteq> (b, j)"
    from split_list[OF ai] obtain bs1 bs2 where bs: "bs = bs1 @ (a,i) # bs2" by auto
    with bj diff have "(b,j) \<in> set (bs1 @ bs2)" by auto
    from split_list[OF this] obtain cs1 cs2 where cs: "bs1 @ bs2 = cs1 @ (b,j) # cs2" by auto
    have "prod_list (map fst bs) = a * prod_list (map fst (bs1 @ bs2))" unfolding bs by simp
    also have "\<dots> = a * b * prod_list (map fst (cs1 @ cs2))" unfolding cs by simp
    finally obtain c where lp: "prod_list (map fst bs) = a * b * c" by auto
    from deg[OF ai] have 0: "gcd a b \<noteq> 0" by auto
    have gcd: "gcd a b * gcd a b dvd prod_list (map fst bs)" 
      unfolding lp by (simp add: mult_dvd_mono)
    {
      assume "degree (gcd a b) > 0"
      from sf[unfolded square_free_def, THEN conjunct2, rule_format, OF this] gcd
      have False by simp
    }
    hence "degree (gcd a b) = 0" by auto
    with 0 show "coprime a b" using is_unit_gcd is_unit_iff_degree by blast
  }
qed

lemma square_free_factorization_def': fixes p :: "'a poly"
  shows "square_free_factorization p (c,bs) \<longleftrightarrow>
  (p = smult c (\<Prod>(a, i) \<leftarrow> bs. a ^ Suc i)) \<and>
  (square_free (prod_list (map fst bs))) \<and>
  (\<forall> b i. (b,i) \<in> set bs \<longrightarrow> degree b > 0) \<and>
  (p = 0 \<longrightarrow> c = 0 \<and> bs = [])"
  using square_free_factorizationD'[of p c bs]
  square_free_factorizationI'[of p c bs] by blast

lemma square_free_factorization_smult_prod_listI: fixes p :: "'a poly"
  assumes sff: "square_free_factorization p (c, bs1 @ (smult b (prod_list bs),i) # bs2)"
  and bs: "\<And> b. b \<in> set bs \<Longrightarrow> degree b > 0"
  shows "square_free_factorization p (c * b^(Suc i), bs1 @ map (\<lambda> b. (b,i)) bs @ bs2)"
proof -
  from square_free_factorizationD'(3)[OF sff, of "smult b (prod_list bs)" i]
  have b: "b \<noteq> 0" by auto
  note sff = square_free_factorizationD'[OF sff]
  show ?thesis
  proof (intro square_free_factorizationI', goal_cases)
    case 1
    thus ?case unfolding sff(1) by (simp add: o_def field_simps smult_power prod_list_pow_suc)
  next
    case 2
    show ?case using sff(2) by (simp add: ac_simps o_def square_free_smult_iff[OF b])
  next
    case 3
    with sff(3) bs show ?case by auto
  next
    case 4
    from sff(4)[OF this] show ?case by simp
  qed
qed

lemma square_free_factorization_further_factorization: fixes p :: "'a poly"
  assumes sff: "square_free_factorization p (c, bs)"
  and bs: "\<And> b i d fs. (b,i) \<in> set bs \<Longrightarrow> f b = (d,fs) 
    \<Longrightarrow> b = smult d (prod_list fs) \<and> (\<forall> f \<in> set fs. degree f > 0)"
  and h: "h = (\<lambda> (b,i). case f b of (d,fs) \<Rightarrow> (d^Suc i,map (\<lambda> f. (f,i)) fs))"
  and gs: "gs = map h bs"
  and d: "d = c * prod_list (map fst gs)"
  and es: "es = concat (map snd gs)"
  shows "square_free_factorization p (d, es)"
proof -
  note sff = square_free_factorizationD'[OF sff]
  show ?thesis
  proof (rule square_free_factorizationI')
    assume "p = 0" 
    from sff(4)[OF this] show "d = 0 \<and> es = []" unfolding d es gs by auto
  next
    have id: "(\<Prod>(a, i)\<leftarrow>bs. a * a ^ i) = smult (prod_list (map fst gs)) (\<Prod>(a, i)\<leftarrow>es. a * a ^ i)"
      unfolding es gs h map_map o_def using bs
    proof (induct bs)
      case (Cons bi bs)
      obtain b i where bi: "bi = (b,i)" by force
      obtain d fs where f: "f b = (d,fs)" by force
      from Cons(2)[OF _ f, of i] have b: "b = smult d (prod_list fs)" unfolding bi by auto
      note IH = Cons(1)[OF Cons(2), of "\<lambda> _ i _ _ . i"]
      show ?case unfolding bi
        by (simp add: f o_def, simp add: b ac_simps, subst IH, 
          auto simp: smult_power prod_list_pow_suc ac_simps)
    qed simp
    show "p = smult d (\<Prod>(a, i)\<leftarrow>es. a ^ Suc i)" unfolding sff(1) using id
      by (simp add: d)
  next
    fix fi i
    assume fi: "(fi, i) \<in> set es"
    from this[unfolded es] obtain G where G: "G \<in> snd ` set gs" and fi: "(fi,i) \<in> set G" by auto
    from G[unfolded gs] obtain b i where bi: "(b,i) \<in> set bs" 
      and G: "G = snd (h (b,i))" by auto 
    obtain d fs where f: "f b = (d,fs)" by force
    show "degree fi > 0"
      by (rule bs[THEN conjunct2, rule_format, OF bi f], insert fi G f, unfold h, auto)
  next
    have id: "\<exists> c. prod_list (map fst bs) = smult c (prod_list (map fst es))"
      unfolding es gs map_map o_def using bs
    proof (induct bs)
      case (Cons bi bs)
      obtain b i where bi: "bi = (b,i)" by force
      obtain d fs where f: "f b = (d,fs)" by force
      from Cons(2)[OF _ f, of i] have b: "b = smult d (prod_list fs)" unfolding bi by auto
      have "\<exists>c. prod_list (map fst bs) = smult c (prod_list (map fst (concat (map (\<lambda>x. snd (h x)) bs))))"
        by (rule Cons(1), rule Cons(2), auto)
      then obtain c where 
        IH: "prod_list (map fst bs) = smult c (prod_list (map fst (concat (map (\<lambda>x. snd (h x)) bs))))" by auto
      show ?case unfolding bi
        by (intro exI[of _ "c * d"], auto simp: b IH, auto simp: h f[unfolded b] o_def)
    qed (intro exI[of _ 1], auto)
    then obtain c where "prod_list (map fst bs) = smult c (prod_list (map fst es))" by blast
    from sff(2)[unfolded this] show "square_free (prod_list (map fst es))"
      by (metis smult_eq_0_iff square_free_def square_free_smult_iff)
  qed
qed

lemma square_free_factorization_prod_listI: fixes p :: "'a poly"
  assumes sff: "square_free_factorization p (c, bs1 @ ((prod_list bs),i) # bs2)"
  and bs: "\<And> b. b \<in> set bs \<Longrightarrow> degree b > 0"
  shows "square_free_factorization p (c, bs1 @ map (\<lambda> b. (b,i)) bs @ bs2)"
  using square_free_factorization_smult_prod_listI[of p c bs1 1 bs i bs2] sff bs by auto

lemma square_free_factorization_factorI: fixes p :: "'a poly"
  assumes sff: "square_free_factorization p (c, bs1 @ (a,i) # bs2)"
  and r: "degree r \<noteq> 0" and s: "degree s \<noteq> 0"
  and a: "a = r * s"
  shows "square_free_factorization p (c, bs1 @ ((r,i) # (s,i) # bs2))"
  using square_free_factorization_prod_listI[of p c bs1 "[r,s]" i bs2] sff r s a by auto

end

lemma monic_square_free_irreducible_factorization: assumes mon: "monic (f :: 'b :: field poly)" 
  and sf: "square_free f"
  shows "\<exists> P. finite P \<and> f = \<Prod>P \<and> P \<subseteq> {q. irreducible q \<and> monic q}"
proof -
  from mon have f0: "f \<noteq> 0" by auto
  from monic_irreducible_factorization[OF assms(1)] obtain P n where
    P: "finite P" "P \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}" and f: "f = (\<Prod>a\<in>P. a ^ Suc (n a))" by auto
  have *: "\<forall> a \<in> P. n a = 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain a where a: "a \<in> P" and n: "n a \<noteq> 0" by auto
    have "f = a ^ (Suc (n a)) * (\<Prod>b\<in>P - {a}. b ^ Suc (n b))"
      unfolding f by (rule prod.remove[OF P(1) a])
    with n have "a * a dvd f" by (cases "n a", auto)
    with sf[unfolded square_free_def] f0 have "degree a = 0" by auto
    with a P(2)[unfolded irreducible\<^sub>d_def] show False by auto
  qed
  have "f = \<Prod> P" unfolding f
    by (rule prod.cong[OF refl], insert *, auto)
  with P show ?thesis by auto
qed

context 
  assumes "SORT_CONSTRAINT('a :: {field, factorial_ring_gcd})" 
begin
lemma monic_factorization_uniqueness:
fixes P::"'a poly set"
assumes finite_P: "finite P" 
  and PQ: "\<Prod>P = \<Prod>Q" 
  and P: "P \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
and finite_Q: "finite Q" 
  and Q: "Q \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
shows "P = Q" 
proof (rule; rule subsetI)
  fix x assume x: "x \<in> P"
  have irr_x: "irreducible x" using x P by auto
  then have "\<exists>a\<in>Q. x dvd id a"
  proof (rule irreducible_dvd_prod)
    show "x dvd prod id Q" using PQ x 
      by (metis dvd_refl dvd_prod finite_P id_apply prod.cong)
  qed
  from this obtain a where a: "a\<in>Q" and x_dvd_a: "x dvd a" unfolding id_def by blast
  have "x=a" using x P a Q irreducible\<^sub>d_dvd_eq[OF _ _ x_dvd_a] by fast
  thus "x \<in> Q" using a by simp
next
  fix x assume x: "x \<in> Q"
  have irr_x: "irreducible x" using x Q by auto
  then have "\<exists>a\<in>P. x dvd id a"
  proof (rule irreducible_dvd_prod)
    show "x dvd prod id P" using PQ x 
      by (metis dvd_refl dvd_prod finite_Q id_apply prod.cong)
  qed
  from this obtain a where a: "a\<in>P" and x_dvd_a: "x dvd a" unfolding id_def by blast
  have "x=a" using x P a Q irreducible\<^sub>d_dvd_eq[OF _ _ x_dvd_a] by fast
  thus "x \<in> P" using a by simp
qed
end

subsection \<open>Yun factorization and homomorphisms\<close>

locale field_hom_0' = field_hom hom
  for hom :: "'a :: {field_char_0,euclidean_ring_gcd} \<Rightarrow> 'b :: {field_char_0,euclidean_ring_gcd}"
begin
  sublocale field_hom' ..
end

lemma (in field_hom_0') yun_factorization_main_hom:
  defines hp: "hp \<equiv> map_poly hom"
  defines hpi: "hpi \<equiv> map (\<lambda> (f,i). (hp f, i :: nat))"
  assumes monic: "monic p" and f: "f = p div gcd p (pderiv p)" and g: "g = pderiv p div gcd p (pderiv p)"
  shows "yun_gcd.yun_factorization_main gcd (hp f) (hp g) i (hpi as) = hpi (yun_gcd.yun_factorization_main gcd f g i as)"
proof -
  let ?P = "\<lambda> f g. \<forall> i as. yun_gcd.yun_factorization_main gcd (hp f) (hp g) i (hpi as) = hpi (yun_gcd.yun_factorization_main gcd f g i as)"
  note ind = yun_factorization_induct[OF _ _ f g monic, of ?P, rule_format]
  interpret map_poly_hom: map_poly_inj_comm_ring_hom..
  interpret p: inj_comm_ring_hom hp unfolding hp..
  note homs = map_poly_gcd[folded hp] 
      map_poly_pderiv[folded hp] 
      p.hom_minus 
      map_poly_div[folded hp]
  show ?thesis
  proof (induct rule: ind)
    case (1 f g i as)
    show ?case unfolding yun_gcd.yun_factorization_main.simps[of _ "hp f"] yun_gcd.yun_factorization_main.simps[of _ f]
      unfolding 1 by simp
  next
    case (2 f g i as)
    have id: "\<And> f i fis. hpi ((f,i) # fis) = (hp f, i) # hpi fis" unfolding hpi by auto
    show ?case unfolding yun_gcd.yun_factorization_main.simps[of _ "hp f"] yun_gcd.yun_factorization_main.simps[of _ f]
      unfolding "p.hom_1_iff"
      unfolding Let_def
      unfolding homs[symmetric] id[symmetric]
      unfolding 2(2) by simp
  qed
qed

lemma square_free_square_free_factorization: 
  "square_free (p :: 'a :: {field,factorial_ring_gcd} poly) \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow> square_free_factorization p (1,[(p,0)])"
  by (intro square_free_factorizationI', auto)

lemma constant_square_free_factorization: 
  "degree p = 0 \<Longrightarrow> square_free_factorization p (coeff p 0,[])"
  by (drule degree0_coeffs [of p]) (auto simp: square_free_factorization_def)

lemma (in field_hom_0') yun_monic_factorization:
  defines hp: "hp \<equiv> map_poly hom"
  defines hpi: "hpi \<equiv> map (\<lambda> (f,i). (hp f, i :: nat))"
  assumes monic: "monic f"
  shows "yun_gcd.yun_monic_factorization gcd (hp f) = hpi (yun_gcd.yun_monic_factorization gcd f)"
proof -
  interpret map_poly_hom: map_poly_inj_comm_ring_hom..
  interpret p: inj_ring_hom hp unfolding hp..
  have hpiN: "hpi [] = []" unfolding hpi by simp
  obtain res where "res = 
    yun_gcd.yun_factorization_main gcd (f div gcd f (pderiv f)) (pderiv f div gcd f (pderiv f)) 0 []" by auto
  note homs = map_poly_gcd[folded hp] 
      map_poly_pderiv[folded hp] 
      p.hom_minus 
      map_poly_div[folded hp]
      yun_factorization_main_hom[folded hp, folded hpi, symmetric, OF monic refl refl, of _ Nil, unfolded hpiN]
      this   
  show ?thesis
    unfolding yun_gcd.yun_monic_factorization_def Let_def
    unfolding homs[symmetric]
    unfolding hpi
      by (induct res, auto)
qed


lemma (in field_hom_0') yun_factorization_hom:
  defines hp: "hp \<equiv> map_poly hom"
  defines hpi: "hpi \<equiv> map (\<lambda> (f,i). (hp f, i :: nat))"
  shows "yun_factorization gcd (hp f) = map_prod hom hpi (yun_factorization gcd f)"
  using yun_monic_factorization[of "smult (inverse (coeff f (degree f))) f"]
  unfolding yun_factorization_def Let_def hp hpi
   by (auto simp: hom_distribs)

lemma (in field_hom_0') square_free_map_poly:
  "square_free (map_poly hom f) = square_free f"
proof -
  interpret map_poly_hom: map_poly_inj_comm_ring_hom..
  show ?thesis unfolding square_free_iff_separable separable_def
    by (simp only: hom_distribs [symmetric] (*fold doesn't work!*))
      (simp add: coprime_iff_gcd_eq_1 map_poly_gcd [symmetric])
qed

end
