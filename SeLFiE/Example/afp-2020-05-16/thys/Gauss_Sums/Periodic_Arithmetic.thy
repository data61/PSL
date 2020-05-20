(*
  File:     Periodic_Arithmetic.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  Periodic arithmetic functions
*)
section \<open>Periodic arithmetic functions\<close>
theory Periodic_Arithmetic
imports
  Complex_Main
  "HOL-Number_Theory.Cong"
begin

definition 
  "periodic_arithmetic f k = (\<forall>n. f (n+k) = f n)" 
  for n :: int and k :: nat and f :: "nat \<Rightarrow> complex"

lemma const_periodic_arithmetic: "periodic_arithmetic (\<lambda>x. y) k"
  unfolding periodic_arithmetic_def by blast

lemma add_periodic_arithmetic:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "periodic_arithmetic f k"
  assumes "periodic_arithmetic g k"
  shows "periodic_arithmetic (\<lambda>n. f n + g n) k"
  using assms unfolding periodic_arithmetic_def by simp

lemma mult_periodic_arithmetic:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "periodic_arithmetic f k"
  assumes "periodic_arithmetic g k"
  shows "periodic_arithmetic (\<lambda>n. f n * g n) k"
  using assms unfolding periodic_arithmetic_def  by simp

lemma scalar_mult_periodic_arithmetic:
  fixes f :: "nat \<Rightarrow> complex" and a :: complex
  assumes "periodic_arithmetic f k"
  shows "periodic_arithmetic (\<lambda>n. a * f n) k"
  using mult_periodic_arithmetic[OF const_periodic_arithmetic[of a k] assms(1)] by simp

lemma fin_sum_periodic_arithmetic_set:
  fixes f g :: "nat \<Rightarrow> complex" 
  assumes "\<forall>i\<in>A. periodic_arithmetic (h i) k"
  shows "periodic_arithmetic (\<lambda>n. \<Sum>i \<in> A. h i n) k"
  using assms by (simp add: periodic_arithmetic_def)

lemma mult_period:
  assumes "periodic_arithmetic g k"
  shows "periodic_arithmetic g (k*q)"
  using assms
proof (induction q)
  case 0 then show ?case unfolding periodic_arithmetic_def by simp
next
  case (Suc m)
  then show ?case 
    unfolding periodic_arithmetic_def 
  proof -
   { fix n 
     have "g (n + k * Suc m) = g (n + k +  k * m)"
       by (simp add: algebra_simps)
     also have "\<dots> = g(n)" 
       using Suc.IH[OF Suc.prems] assms
       unfolding periodic_arithmetic_def by simp
     finally have "g (n + k * Suc m) = g(n)" by blast
   }
    then show "\<forall>n. g (n + k * Suc m) = g n" by auto
  qed   
qed

lemma unique_periodic_arithmetic_extension:
  assumes "k > 0"
  assumes "\<forall>j<k. g j = h j"
  assumes "periodic_arithmetic g k" and "periodic_arithmetic h k"
  shows "g i = h i"
proof (cases "i < k")
  case True then show ?thesis using assms by simp
next
  case False then show ?thesis 
  proof -
    have "k * (i div k) + (i mod k) = i \<and> (i mod k) < k" 
      by (simp add: assms(1) algebra_simps)
    then obtain q r where euclid_div: "k*q + r = i \<and> r < k"
      using mult.commute by blast
    from assms(3) assms(4) 
    have  "periodic_arithmetic g (k*q)" "periodic_arithmetic h (k*q)" 
      using mult_period by simp+
    have "g(k*q+r) = g(r)" 
      using \<open>periodic_arithmetic g (k*q)\<close> unfolding periodic_arithmetic_def 
      using add.commute[of "k*q" r] by presburger
    also have "\<dots> = h(r)" 
      using euclid_div assms(2) by simp
    also have "\<dots> = h(k*q+r)"
      using \<open>periodic_arithmetic h (k*q)\<close> add.commute[of "k*q" r]
      unfolding periodic_arithmetic_def by presburger
    also have "\<dots> = h(i)" using euclid_div by simp
    finally show "g(i) = h(i)" using euclid_div by simp
  qed
qed
                  
lemma periodic_arithmetic_sum_periodic_arithmetic:
  assumes "periodic_arithmetic f k"
  shows "(\<Sum>l \<in> {m..n}. f l) = (\<Sum>l \<in> {m+k..n+k}. f l)"
  using periodic_arithmetic_def assms 
  by (intro sum.reindex_bij_witness
         [of "{m..n}" "\<lambda>l. l-k" "\<lambda>l. l+k" "{m+k..n+k}" f f])
      auto

lemma mod_periodic_arithmetic:
  fixes n m :: nat
  assumes "periodic_arithmetic f k"
  assumes "n mod k = m mod k"
  shows "f n = f m"
proof -
  obtain q where 1: "n = q*k+(n mod k)"   
     using div_mult_mod_eq[of n k,symmetric] by blast 
  obtain q' where 2: "m = q'*k+(m mod k)"
     using div_mult_mod_eq[of m k,symmetric] by blast
  from 1 have "f n = f (q*k+(n mod k))" by auto
  also have "\<dots> = f (n mod k)"
    using mult_period[of f k q] assms(1) periodic_arithmetic_def[of f "k*q"]
    by (simp add: algebra_simps,subst add.commute,blast)
  also have "\<dots> = f (m mod k)" using assms(2) by auto
  also have "\<dots> = f (q'*k+(m mod k))"
    using mult_period[of f k q'] assms(1) periodic_arithmetic_def[of f "k*q'"]
    by (simp add: algebra_simps,subst add.commute,presburger)
  also have "\<dots> = f m" using 2 by auto
  finally show "f n = f m" by simp
qed

lemma cong_periodic_arithmetic:
  assumes "periodic_arithmetic f k" "[a = b] (mod k)"
  shows   "f a = f b"
  using assms mod_periodic_arithmetic[of f k a b] by (auto simp: cong_def)

lemma cong_nat_imp_eq:
  fixes m :: nat
  assumes "m > 0" "x \<in> {a..<a+m}" "y \<in> {a..<a+m}" "[x = y] (mod m)"
  shows   "x = y"
  using assms
proof (induction x y rule: linorder_wlog)
  case (le x y)
  have "[y - x = 0] (mod m)"
    using cong_diff_iff_cong_0_nat cong_sym le by blast
  thus "x = y"
    using le by (auto simp: cong_def)
qed (auto simp: cong_sym)

lemma inj_on_mod_nat:
  fixes m :: nat
  assumes "m > 0"
  shows   "inj_on (\<lambda>x. x mod m) {a..<a+m}"
proof
  fix x y assume xy: "x \<in> {a..<a+m}" "y \<in> {a..<a+m}" and eq: "x mod m = y mod m"
  from \<open>m > 0\<close> and xy show "x = y"
    by (rule cong_nat_imp_eq) (use eq in \<open>simp_all add: cong_def\<close>)
qed

lemma bij_betw_mod_nat_atLeastLessThan:
  fixes k d :: nat
  assumes "k > 0"
  defines "g \<equiv> (\<lambda>i. nat ((int i - int d) mod int k) + d)"
  shows   "bij_betw (\<lambda>i. i mod k) {d..<d+k} {..<k}"
  unfolding bij_betw_def
proof
  show inj: "inj_on (\<lambda>i. i mod k) {d..<d + k}"
    by (rule inj_on_mod_nat) fact+
  have "(\<lambda>i. i mod k) ` {d..<d + k} \<subseteq> {..<k}"
    by auto
  moreover have "card ((\<lambda>i. i mod k) ` {d..<d + k}) = card {..<k}"
    using inj by (subst card_image) auto
  ultimately show "(\<lambda>i. i mod k) ` {d..<d + k} = {..<k}"
    by (intro card_subset_eq) auto
qed

lemma periodic_arithmetic_sum_periodic_arithmetic_shift:
  fixes k d :: nat
  assumes "periodic_arithmetic f k" "k > 0" "d > 0"
  shows "(\<Sum>l \<in> {0..k-1}. f l) = (\<Sum>l \<in> {d..d+k-1}. f l)"
proof -
  have "(\<Sum>l \<in> {0..k-1}. f l) = (\<Sum>l \<in> {0..<k}. f l)"
    using assms(2) by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>l \<in> {d..<d+k}. f (l mod k))"
    using assms(2) 
    by (simp add: sum.reindex_bij_betw[OF bij_betw_mod_nat_atLeastLessThan[of k d]] 
                  lessThan_atLeast0)
  also have "\<dots> = (\<Sum>l \<in> {d..<d+k}. f l)"
    using mod_periodic_arithmetic[of f k] assms(1) sum.cong
    by (meson mod_mod_trivial)
  also have "\<dots> = (\<Sum>l \<in> {d..d+k-1}. f l)"
    using assms(2,3) by (intro sum.cong) auto
  finally show ?thesis by auto
qed

lemma self_bij_0_k:
  fixes a k :: nat
  assumes "coprime a k" "[a*i = 1] (mod k)" "k > 0" 
  shows "bij_betw (\<lambda>r. r*a mod k) {0..k-1} {0..k-1}"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>r. r*a mod k) {0..k-1}"
  proof -
    {fix r1 r2
    assume in_k: "r1 \<in> {0..k-1}" "r2 \<in> {0..k-1}"
    assume as: "[r1*a = r2*a] (mod k)"
    then have "[r1*a*i = r2*a*i] (mod k)" 
      using cong_scalar_right by blast
    then have "[r1 = r2] (mod k)" 
      using cong_mult_rcancel_nat as assms(1) by simp
    then have "r1 = r2" using in_k
      using assms(3) cong_less_modulus_unique_nat by auto}
    note eq = this
    show ?thesis unfolding inj_on_def 
      by (safe, simp add: eq cong_def)
  qed
  define f where "f = (\<lambda>r. r * a mod k)"
  show "f ` {0..k - 1} = {0..k - 1} "
    unfolding image_def
  proof (standard)
    show "{y. \<exists>x\<in>{0..k - 1}. y = f x} \<subseteq> {0..k - 1}" 
    proof -
      {fix y
      assume "y \<in> {y. \<exists>x\<in>{0..k - 1}. y = f x}" 
      then obtain x where "y = f x" by blast
      then have "y \<in> {0..k-1}"
        unfolding f_def
        using Suc_pred assms(3) lessThan_Suc_atMost by fastforce}
      then show ?thesis by blast
    qed
    show "{0..k - 1} \<subseteq> {y. \<exists>x\<in>{0..k - 1}. y = f x}"
    proof -
      { fix x 
        assume ass: "x \<in> {0..k-1}"
        then have "x * i mod k \<in> {0..k-1}"
        proof -
          have "x * i mod k \<in> {0..<k}" by (simp add: assms(3))
          have "{0..<k} = {0..k-1}" using Suc_diff_1 assms(3) by auto
          show ?thesis using \<open>x * i mod k \<in> {0..<k}\<close> \<open>{0..<k} = {0..k-1}\<close> by blast
        qed          
        then have "f (x * i mod k) = x"
        proof -
          have "f (x * i mod k) = (x * i mod k) * a mod k"
            unfolding f_def by blast
          also have "\<dots> = (x*i*a) mod k" 
            by (simp add: mod_mult_left_eq) 
          also have "\<dots> = (x*1) mod k" 
            using assms(2) 
            unfolding cong_def 
            by (subst mult.assoc, subst (2) mult.commute,
               subst mod_mult_right_eq[symmetric],simp) 
          also have "\<dots> = x" using ass assms(3) by auto
          finally show ?thesis .
        qed
        then have "x \<in> {y. \<exists>x\<in>{0..k - 1}. y = f x}" 
          using \<open>x * i mod k \<in> {0..k-1}\<close> by force
      }
      then show ?thesis by blast 
    qed
  qed
qed

lemma periodic_arithmetic_homothecy:
  assumes "periodic_arithmetic f k"
  shows   "periodic_arithmetic (\<lambda>l. f (l*a)) k"
  unfolding periodic_arithmetic_def
proof 
  fix n
  have "f ((n + k) * a) = f(n*a+k*a)" by (simp add: algebra_simps)
  also have "\<dots> = f(n*a)" 
    using mult_period[OF assms] unfolding periodic_arithmetic_def by simp
  finally show "f ((n + k) * a) = f (n * a)" by simp
qed

theorem periodic_arithmetic_remove_homothecy:
  assumes "coprime a k" "periodic_arithmetic f k" "k > 0" 
  shows "(\<Sum>l=1..k. f l) = (\<Sum>l=1..k. f (l*a))" 
proof -
  obtain i where inv: "[a*i = 1] (mod k)"
    using assms(1) coprime_iff_invertible_nat[of a k] by auto
  from this self_bij_0_k assms
  have bij: "bij_betw (\<lambda>r. r * a mod k) {0..k - 1} {0..k - 1}" by blast
  
  have "(\<Sum>l = 1..k. f(l)) = (\<Sum>l = 0..k-1. f(l))"
    using periodic_arithmetic_sum_periodic_arithmetic_shift[of f k 1] assms by simp
  also have "\<dots> = (\<Sum>l = 0..k-1. f(l*a mod k))"
    using sum.reindex_bij_betw[OF bij,symmetric] by blast
  also have "\<dots> = (\<Sum>l = 0..k-1. f(l*a))"
    by (intro sum.cong refl) (use mod_periodic_arithmetic[OF assms(2)] mod_mod_trivial in blast)
  also have "\<dots> = (\<Sum>l = 1..k. f(l*a))"
    using periodic_arithmetic_sum_periodic_arithmetic_shift[of "(\<lambda>l. f(l*a))" k 1]
          periodic_arithmetic_homothecy[OF assms(2)] assms(3) by fastforce  
  finally show ?thesis by blast     
qed

end