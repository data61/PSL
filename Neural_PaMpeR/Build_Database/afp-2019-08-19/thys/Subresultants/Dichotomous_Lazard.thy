section \<open>Dichotomous Lazard\<close>
  
text \<open>This theory contains Lazard's optimization in the computation of
  the subresultant PRS as described by Ducos \cite[Section 2]{Ducos}.\<close>
theory Dichotomous_Lazard
imports 
  "HOL-Computational_Algebra.Polynomial_Factorial" (* to_fract *)
begin
  
lemma power_fract[simp]: "(Fract a b)^n = Fract (a^n) (b^n)" 
  by (induct n, auto simp: fract_collapse) 
  
lemma range_to_fract_dvd_iff: assumes b: "b \<noteq> 0" 
  shows "Fract a b \<in> range to_fract \<longleftrightarrow> b dvd a"
proof
  assume "b dvd a" then obtain c where a: "a = b * c" unfolding dvd_def by auto
  have "Fract a b = Fract c 1" using b unfolding a by (simp add: eq_fract)
  thus "Fract a b \<in> range to_fract" unfolding to_fract_def by auto
next
  assume "Fract a b \<in> range to_fract" 
  then obtain c where "Fract a b = Fract c 1" unfolding to_fract_def by auto
  hence "a = b * c" using b by (simp add: eq_fract)
  thus "b dvd a" ..
qed
  
lemma Fract_cases_coprime [cases type: fract]:
  fixes q :: "'a :: factorial_ring_gcd fract" 
  obtains (Fract) a b where "q = Fract a b" "b \<noteq> 0" "coprime a b" 
proof -
  obtain a b where q: "q = Fract a b" and b0: "b \<noteq> 0" by (cases q, auto)
  define g where g: "g = gcd a b" 
  define A where A: "A = a div g" 
  define B where B: "B = b div g" 
  have a: "a = A * g" unfolding A g by simp
  have b: "b = B * g" unfolding B g by simp
  from b0 b have 0: "B \<noteq> 0" by auto
  have q: "q = Fract A B" unfolding q a b
    by (subst eq_fract, auto simp: b0 0 g)
  have cop: "coprime A B" unfolding A B g using b0
    by (simp add: div_gcd_coprime)
  assume "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> coprime a b \<Longrightarrow> thesis" 
  from this[OF q 0 cop] show ?thesis .
qed
  
lemma to_fract_power_le: fixes a :: "'a :: factorial_ring_gcd fract"
  assumes no_fract: "a * b ^ e \<in> range to_fract" 
  and a: "a \<in> range to_fract" 
  and le: "f \<le> e" 
shows "a * b ^ f \<in> range to_fract" 
proof -
  obtain bn bd where b: "b = Fract bn bd" and bd: "bd \<noteq> 0" and copb: "coprime bn bd" by (cases b, auto)
  obtain an where a: "a = Fract an 1" using a unfolding to_fract_def by auto
  have id: "a * b ^ e = Fract (an * bn^e) (bd^e)" unfolding a b power_fract mult_fract by simp
  have 0: "bd^e \<noteq> 0" for e using bd by auto
  from no_fract[unfolded id range_to_fract_dvd_iff[OF 0]] have dvd: "bd ^ e dvd an * bn ^ e" .
  from copb have copb: "coprime (bd ^ e) (bn ^ e)" for e
    by (simp add: ac_simps)
  from dvd copb [of e] bd have "bd ^ e dvd an"
    by (simp add: coprime_dvd_mult_left_iff)
  hence "bd ^ f dvd an" using le by (rule power_le_dvd)
  hence dvd: "bd ^ f dvd an * bn ^ f" by simp
  from le obtain g where e: "e = f + g" using le_Suc_ex by blast
  have id': "a * b ^ f = Fract (an * bn^f) (bd^f)" unfolding a b power_fract mult_fract by simp
  show ?thesis unfolding id' range_to_fract_dvd_iff[OF 0] by (rule dvd)
qed
  
lemma div_divide_to_fract: assumes "x \<in> range to_fract"
  and "x = (y :: 'a :: idom_divide fract) / z" 
  and "x' = y' div z'"
  and "y = to_fract y'" "z = to_fract z'"   
  shows "x = to_fract x'" 
proof (cases "z' = 0")
  case True
  thus ?thesis using assms by auto
next
  case False    
  from assms obtain r where "to_fract y' / to_fract z' = to_fract r" by auto
  thus ?thesis using False assms
    by (simp add: eq_fract(1) to_fract_def)
qed
  
declare divmod_nat_def[termination_simp]

fun dichotomous_Lazard :: "'a :: idom_divide \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "dichotomous_Lazard x y n = (if n \<le> 1 then if n = 1 then x else 1 else
    let (d,r) = Divides.divmod_nat n 2; 
       rec = dichotomous_Lazard x y d;
       recsq = rec * rec div y in 
    if r = 0 then recsq else recsq * x div y)"
  
lemma dichotomous_Lazard_main: fixes x :: "'a :: idom_divide" 
  assumes "\<And> i. i \<le> n \<Longrightarrow> (to_fract x)^i / (to_fract y)^(i - 1) \<in> range to_fract"
  shows "to_fract (dichotomous_Lazard x y n) = (to_fract x)^n / (to_fract y)^(n-1)" 
  using assms
proof (induct x y n rule: dichotomous_Lazard.induct)
  case (1 x y n)
  let ?f = to_fract
  consider (0) "n = 0" | (1) "n = 1" | (n) "\<not> n \<le> 1" by linarith   
  thus ?case
  proof cases
    case n
    obtain d r where n2: "Divides.divmod_nat n 2 = (d,r)" by force
    from divmod_nat_def[of n 2] n2 have dr: "d = n div 2" "r = n mod 2" by auto
    hence r: "r = 0 \<or> r = 1" by auto
    define rec where "rec = dichotomous_Lazard x y d"      
    let ?sq = "rec * rec div y" 
    have res: "dichotomous_Lazard x y n = (if r = 0 then ?sq else ?sq * x div y)"
      unfolding dichotomous_Lazard.simps[of x y n] n2 Let_def rec_def using n by auto
    have ndr: "n = d + d + r" unfolding dr by presburger
    from ndr r n have d0: "d \<noteq> 0" by auto
    have IH: "?f rec = ?f x ^ d / ?f y ^ (d - 1)" 
      using 1(1)[OF n refl n2[symmetric] 1(2), folded rec_def] ndr by auto
    have "?f (rec * rec) = ?f x ^ d / ?f y ^ (d - 1) * ?f x ^ d / ?f y ^ (d - 1)" using IH by simp
    also have "\<dots> = ?f x ^ (d + d) / ?f y ^ (d - 1 + (d - 1))" unfolding power_add by simp
    also have "d - 1 + (d - 1) = d + d - 2" using d0 by simp
    finally have id: "?f (rec * rec) = ?f x ^ (d + d) / ?f y ^ (d + d - 2)"  . 
    let ?dd = "(?f x ^ (d + d) / ?f y ^ (d + d - 2)) / ?f y" 
    let ?d = "?f x ^ (d + d) / ?f y ^ (d + d - 1)" 
    have dd: "?dd = ?d" using d0 by (cases d, auto)
    have sq: "?f ?sq = ?d" unfolding dd[symmetric]
    proof (rule sym, rule div_divide_to_fract[OF _ refl refl id[symmetric] refl], unfold dd)
      show "?d \<in> range ?f" by (rule 1(2), insert ndr, auto)
    qed    
    show ?thesis 
    proof (cases "r = 0")
      case True
      with res sq show ?thesis unfolding ndr by auto
    next
      case False
      with r have r: "r = 1" by auto
      let ?sq' = "?sq * x div y" 
      from False res have res: "dichotomous_Lazard x y n = ?sq'" by simp
      from sq have id: "?f (?sq * x) = ?f x ^ (d + d + r) / ?f y ^ (d + d - 1)" 
        unfolding r by simp
      let ?dd = "(?f x ^ (d + d + r) / ?f y ^ (d + d - 1)) / ?f y" 
      let ?d = "?f x ^ (d + d + r) / ?f y ^ (d + d + r - 1)" 
      have dd: "?dd = ?d" using d0 unfolding r by (cases d, auto)
      have sq': "?f ?sq' = ?d" unfolding dd[symmetric]
      proof (rule sym, rule div_divide_to_fract[OF _ refl refl id[symmetric] refl], unfold dd)
        show "?d \<in> range ?f" by (rule 1(2), unfold ndr, auto)
      qed
      show ?thesis unfolding res sq' unfolding ndr by simp
    qed
  qed auto
qed
    
lemma dichotomous_Lazard: fixes x :: "'a :: factorial_ring_gcd" 
  assumes "(to_fract x)^n / (to_fract y)^(n-1) \<in> range to_fract"
  shows "to_fract (dichotomous_Lazard x y n) = (to_fract x)^n / (to_fract y)^(n-1)" 
proof (rule dichotomous_Lazard_main)
  fix i
  assume i: "i \<le> n" 
  show "to_fract x ^ i / to_fract y ^ (i - 1) \<in> range to_fract" 
  proof (cases i)
    case (Suc j)
    have id: "to_fract x ^ i / to_fract y ^ (i - 1) = to_fract x * (to_fract x / to_fract y) ^ j"
      unfolding Suc by (simp add: power_divide)
    from Suc i have "n \<noteq> 0" and j: "j \<le> n - 1" by auto
    hence idd: "to_fract x * (to_fract x / to_fract y) ^ (n - 1) = (to_fract x)^n / (to_fract y)^(n-1)" 
      by (cases n, auto simp: power_divide)
    show ?thesis unfolding id
      by (rule to_fract_power_le[OF _ _ j], unfold idd, insert assms, auto)
  next
    case 0
    have "1 = to_fract 1" by simp
    hence "1 \<in> range to_fract" by blast
    thus ?thesis using 0 by auto
  qed
qed
  
declare dichotomous_Lazard.simps[simp del]

end
