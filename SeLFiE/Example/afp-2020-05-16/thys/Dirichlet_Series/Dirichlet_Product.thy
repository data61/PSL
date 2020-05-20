(*
    File:      Dirichlet_Product.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Dirichlet convolution\<close>
theory Dirichlet_Product
  imports
     Complex_Main
     Multiplicative_Function
begin

lemma sum_coprime_dvd_cong:
  "(\<Sum>r | r dvd a. \<Sum>s | s dvd b. f r s) = (\<Sum>r | r dvd a. \<Sum>s | s dvd b. g r s)"
  if "coprime a b" "\<And>r s. coprime r s \<Longrightarrow> r dvd a \<Longrightarrow> s dvd b \<Longrightarrow> f r s = g r s"
using refl proof (rule sum.cong, rule sum.cong)
  fix r s
  assume "r \<in> {r. r dvd a}" and "s \<in> {s. s dvd b}"
  then have "r dvd a" and "s dvd b"
    by simp_all
  moreover from \<open>coprime a b\<close> have "coprime r s"
    using \<open>r dvd a\<close> \<open>s dvd b\<close>
    by (auto intro: coprime_imp_coprime dvd_trans)
  ultimately show "f r s = g r s"
    using that by simp
qed

definition dirichlet_prod :: "(nat \<Rightarrow> 'a :: semiring_0) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "dirichlet_prod f g = (\<lambda>n. \<Sum>d | d dvd n. f d * g (n div d))"

lemma sum_divisors_code:
  assumes "n > (0::nat)"
  shows   "(\<Sum>d | d dvd n. f d) = 
             fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then f d + acc else acc) 1 n 0"
proof -
  have "(\<lambda>d acc. if d dvd n then f d + acc else acc) = (\<lambda>d acc. (if d dvd n then f d else 0) + acc)"
    by (simp add: fun_eq_iff)
  hence "fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then f d + acc else acc) 1 n 0 =
           fold_atLeastAtMost_nat (\<lambda>d acc. (if d dvd n then f d else 0) + acc) 1 n 0"
    by (simp only: )
  also have "\<dots> = (\<Sum>d = 1..n. if d dvd n then f d else 0)"
    by (rule sum_atLeastAtMost_code [symmetric])
  also from assms have "\<dots> = (\<Sum>d | d dvd n. f d)"
    by (intro sum.mono_neutral_cong_right) (auto elim: dvdE dest: dvd_imp_le)
  finally show ?thesis ..
qed

lemma dirichlet_prod_code [code]:
  "dirichlet_prod f g n = (if n = 0 then 0 else
     fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then f d * g (n div d) + acc else acc) 1 n 0)"
  unfolding dirichlet_prod_def by (simp add: sum_divisors_code)
  
lemma dirichlet_prod_0 [simp]: "dirichlet_prod f g 0 = 0"
  by (simp add: dirichlet_prod_def)
    
lemma dirichlet_prod_Suc_0 [simp]: "dirichlet_prod f g (Suc 0) = f (Suc 0) * g (Suc 0)"
  by (simp add: dirichlet_prod_def)

lemma dirichlet_prod_cong [cong]: 
  assumes "(\<And>n. n > 0 \<Longrightarrow> f n = f' n)" "(\<And>n. n > 0 \<Longrightarrow> g n = g' n)"
  shows   "dirichlet_prod f g = dirichlet_prod f' g'"
proof
  fix n :: nat
  show "dirichlet_prod f g n = dirichlet_prod f' g' n"
  proof (cases "n = 0")
    case False
    with assms show ?thesis unfolding dirichlet_prod_def
      by (intro ext sum.cong refl) (auto elim!: dvdE)
  qed simp_all
qed
  
lemma dirichlet_prod_altdef1:
  "dirichlet_prod f g = (\<lambda>n. \<Sum>d | d dvd n. f (n div d) * g d)"
proof
  fix n :: nat
  show "dirichlet_prod f g n = (\<Sum>d | d dvd n. f (n div d) * g d)"
  proof (cases "n = 0")
    case False
    hence "dirichlet_prod f g n = (\<Sum>d | d dvd n. f (n div (n div d)) * g (n div d))"
      unfolding dirichlet_prod_def by (intro sum.cong refl) (auto elim!: dvdE)
    also from False have "\<dots> = (\<Sum>d | d dvd n. f (n div d) * g d)" 
      by (intro sum.reindex_bij_witness[of _ "(div) n" "(div) n"]) (auto elim!: dvdE)
    finally show ?thesis .
  qed simp
qed

lemma dirichlet_prod_altdef2:
  "dirichlet_prod f g = (\<lambda>n. \<Sum>(r,d) | r * d = n. f r * g d)"
proof
  fix n
  show "dirichlet_prod f g n = (\<Sum>(r,d) | r * d = n. f r * g d)"
  proof (cases "n = 0")
    case True
    have "(\<lambda>n::nat. (0, n)) ` UNIV \<subseteq> {(r,d). r * d = 0}" by auto
    moreover have "\<not>finite ((\<lambda>n::nat. (0, n)) ` UNIV)"
      by (subst finite_image_iff) (auto simp: inj_on_def)
    ultimately have "infinite {(r,d). r * d = (0::nat)}"
      by (blast dest: finite_subset)
    with True show ?thesis by simp
  next
    case False
    have "(\<Sum>d | d dvd n. f d * g (n div d)) = (\<Sum>r | r dvd n. (\<Sum>d | d = n div r. f r * g d))"
      by (intro sum.cong refl) auto
    also from False have "\<dots> = (\<Sum>(r,d)\<in>(SIGMA x:{r. r dvd n}. {d. d = n div x}). f r * g d)"
      by (intro sum.Sigma) auto
    also from False have "(SIGMA x:{r. r dvd n}. {d. d = n div x}) = {(r,d). r * d = n}"
      by auto
    finally show ?thesis by (simp add: dirichlet_prod_def)
  qed
qed 
  
lemma dirichlet_prod_commutes:
  "dirichlet_prod (f :: nat \<Rightarrow> 'a :: comm_semiring_0) g = dirichlet_prod g f"
proof
  fix n :: nat
  show "dirichlet_prod f g n = dirichlet_prod g f n"
  proof (cases "n = 0")
    case False
    have "(\<Sum>(r,d) | r * d = n. f r * g d) = (\<Sum>(d,r) | r * d = n. f r * g d)"
      by (rule sum.reindex_bij_witness [of _ "\<lambda>(x,y). (y,x)" "\<lambda>(x,y). (y,x)"]) auto
    thus ?thesis by (simp add: dirichlet_prod_altdef2 mult.commute)
  qed (simp add: dirichlet_prod_def)
qed

lemma finite_divisors_nat': "n > (0 :: nat) \<Longrightarrow> finite {(a,b). a * b = n}"
  by (rule finite_subset[of _ "{0<..n} \<times> {0<..n}"]) auto

lemma dirichlet_prod_assoc_aux1:
  assumes "n > 0"
  shows "dirichlet_prod f (dirichlet_prod g h) n = 
           (\<Sum>(a, b, c)\<in>{(a, b, c). a * b * c = n}. f a * g b * h c)"
proof -
  have "dirichlet_prod f (dirichlet_prod g h) n = 
          (\<Sum>x\<in>{(a,b). a * b = n}. (\<Sum>(c,d) | c * d = snd x. f (fst x) * g c * h d))"
    by (auto intro!: sum.cong simp: dirichlet_prod_altdef2 sum_distrib_left mult.assoc)
  also from assms have "\<dots> = (\<Sum>x\<in>(SIGMA x:{(a, b). a * b = n}. {(c, d). c * d = snd x}).
                               case x of (x, c, d) \<Rightarrow> f (fst x) * g c * h d)"
    by (intro sum.Sigma finite_divisors_nat' ballI) auto
  also have "\<dots> = (\<Sum>(a,b,c) | a * b * c = n. f a * g b * h c)"
    by (rule sum.reindex_bij_witness
               [of _ "\<lambda>(a,b,c). ((a, b*c), (b,c))" "\<lambda>((a,b),(c,d)). (a, c, d)"])
       (auto simp: mult_ac)
  finally show ?thesis .
qed

lemma dirichlet_prod_assoc_aux2:
  assumes "n > 0"
  shows "dirichlet_prod (dirichlet_prod f g) h n = 
           (\<Sum>(a, b, c)\<in>{(a, b, c). a * b * c = n}. f a * g b * h c)"
proof -
  have "dirichlet_prod (dirichlet_prod f g) h n = 
          (\<Sum>x\<in>{(a,b). a * b = n}. (\<Sum>(c,d) | c * d = fst x. f c * g d * h (snd x)))"
    by (auto intro!: sum.cong simp: dirichlet_prod_altdef2 sum_distrib_right mult.assoc)
  also from assms have "\<dots> = (\<Sum>x\<in>(SIGMA x:{(a, b). a * b = n}. {(c, d). c * d = fst x}).
                               case x of (x, c, d) \<Rightarrow> f c * g d * h (snd x))"
    by (intro sum.Sigma finite_divisors_nat' ballI) auto
  also have "\<dots> = (\<Sum>(a,b,c) | a * b * c = n. f a * g b * h c)"
    by (rule sum.reindex_bij_witness
               [of _ "\<lambda>(a,b,c). ((a*b, c), (a,b))" "\<lambda>((a,b),(c,d)). (c, d, b)"])
       (auto simp: mult_ac)
  finally show ?thesis .
qed

lemma dirichlet_prod_assoc: 
  "dirichlet_prod (dirichlet_prod f g) h = dirichlet_prod f (dirichlet_prod g h)"
proof
  fix n :: nat
  show "dirichlet_prod (dirichlet_prod f g) h n = dirichlet_prod f (dirichlet_prod g h) n"
    by (cases "n = 0") (simp_all add: dirichlet_prod_assoc_aux1 dirichlet_prod_assoc_aux2)
qed
    
lemma dirichlet_prod_const_right [simp]:
  assumes "n > 0"
  shows   "dirichlet_prod f (\<lambda>n. if n = Suc 0 then c else 0) n = f n * c"
proof -
  have "dirichlet_prod f (\<lambda>n. if n = Suc 0 then c else 0) n = 
          (\<Sum>d | d dvd n. (if d = n then f n * c else 0))"
    unfolding dirichlet_prod_def using assms
    by (intro sum.cong refl) (auto elim!: dvdE split: if_splits)
  also have "\<dots> = f n * c" using assms by (subst sum.delta) auto
  finally show ?thesis .
qed
  
lemma dirichlet_prod_const_left [simp]:
  assumes "n > 0"
  shows   "dirichlet_prod (\<lambda>n. if n = Suc 0 then c else 0) g n = c * g n"
proof -
  have "dirichlet_prod (\<lambda>n. if n = Suc 0 then c else 0) g n = 
          (\<Sum>d | d dvd n. (if d = 1 then c * g n else 0))"
    unfolding dirichlet_prod_def using assms
    by (intro sum.cong refl) (auto elim!: dvdE split: if_splits)
  also have "\<dots> = c * g n" using assms by (subst sum.delta) auto
  finally show ?thesis .
qed


fun dirichlet_inverse :: "(nat \<Rightarrow> 'a :: comm_ring_1) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "dirichlet_inverse f i n = 
     (if n = 0 then 0 else if n = 1 then i
      else -i * (\<Sum>d | d dvd n \<and> d < n. f (n div d) * dirichlet_inverse f i d))"
  
lemma dirichlet_inverse_induct [case_names 0 1 gt1]:
  "P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> (\<And>n. n > 1 \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> P k) \<Longrightarrow> P n) \<Longrightarrow> P n"
  by induction_schema (force, rule wf_measure [of id], simp)

lemma dirichlet_inverse_0 [simp]: "dirichlet_inverse f i 0 = 0"
  by simp  

lemma dirichlet_inverse_Suc_0 [simp]: "dirichlet_inverse f i (Suc 0) = i"
  by simp

declare dirichlet_inverse.simps [simp del]

lemma dirichlet_inverse_gt_1:
  "n > 1 \<Longrightarrow> dirichlet_inverse f i n =
     -i * (\<Sum>d | d dvd n \<and> d < n. f (n div d) * dirichlet_inverse f i d)"
  by (simp add: dirichlet_inverse.simps)

lemma dirichlet_inverse_cong [cong]:
  assumes "\<And>n. n > 0 \<Longrightarrow> f n = f' n" "i = i'" "n = n'"
  shows   "dirichlet_inverse f i n = dirichlet_inverse f' i' n'"
proof -
  have "dirichlet_inverse f i n = dirichlet_inverse f' i n"
  using assms(1)
  proof (induction n rule: dirichlet_inverse_induct) 
    case (gt1 n)
    have *: "dirichlet_inverse f i k = dirichlet_inverse f' i k" if "k dvd n \<and> k < n" for k
      using that by (intro gt1) auto
    have *: "(\<Sum>d | d dvd n \<and> d < n. f (n div d) * dirichlet_inverse f i d) =
               (\<Sum>d | d dvd n \<and> d < n. f' (n div d) * dirichlet_inverse f' i d)"
      by (intro sum.cong refl) (subst gt1.prems, auto elim: dvdE simp: *)
    consider "n = 0" | "n = 1" | "n > 1" by force
    thus ?case
      by cases (insert *, simp_all add: dirichlet_inverse_gt_1 * cong: sum.cong)
  qed auto
  with assms(2,3) show ?thesis by simp
qed

lemma dirichlet_inverse_gt_1':
  assumes "n > 1"
  shows   "dirichlet_inverse f i n = 
             -i * dirichlet_prod (\<lambda>n. if n = 1 then 0 else f n) (dirichlet_inverse f i) n"
proof -
  have "dirichlet_prod (\<lambda>n. if n = 1 then 0 else f n) (dirichlet_inverse f i) n = 
          (\<Sum>d | d dvd n. (if n div d = Suc 0 then 0 else f (n div d)) * dirichlet_inverse f i d)"
    by (simp add: dirichlet_prod_altdef1)
  also from assms have "\<dots> = (\<Sum>d | d dvd n \<and> d \<noteq> n. f (n div d) * dirichlet_inverse f i d)"
    by (intro sum.mono_neutral_cong_right) (auto elim: dvdE)
  also from assms have "{d. d dvd n \<and> d \<noteq> n} = {d. d dvd n \<and> d < n}" by (auto dest: dvd_imp_le)
  also from assms have "-i * (\<Sum>d\<in>\<dots>. f (n div d) * dirichlet_inverse f i d) = 
                          dirichlet_inverse f i n"
    by (simp add: dirichlet_inverse_gt_1)
  finally show ?thesis ..
qed

lemma of_int_dirichlet_prod: 
  "of_int (dirichlet_prod f g n) = dirichlet_prod (\<lambda>n. of_int (f n)) (\<lambda>n. of_int (g n)) n"
  by (simp add: dirichlet_prod_def)

lemma of_int_dirichlet_inverse: 
  "of_int (dirichlet_inverse f i n) = dirichlet_inverse (\<lambda>n. of_int (f n)) (of_int i) n"
proof (induction n rule: dirichlet_inverse_induct)
  case (gt1 n)
  from gt1 have "(of_int (dirichlet_inverse f i n) :: 'a) = 
    - (of_int i * (\<Sum>d | d dvd n \<and> d < n. of_int (f (n div d) * dirichlet_inverse f i d)))" 
     (is "_ = - (_ * ?A)")
     by (simp add: dirichlet_inverse_gt_1 of_int_dirichlet_prod)
   also have "?A = (\<Sum>d | d dvd n \<and> d < n. of_int (f (n div d)) * 
                  dirichlet_inverse (\<lambda>n. of_int (f n)) (of_int i) d)"
     by (intro sum.cong refl) (auto simp: gt1)
   also have "-(of_int i * \<dots>) = dirichlet_inverse (\<lambda>n. of_int (f n)) (of_int i) n"
     using gt1.hyps by (simp add: dirichlet_inverse_gt_1)
   finally show ?case .
qed simp_all
   
lemma dirichlet_inverse_code [code]:
  "dirichlet_inverse f i n = (if n = 0 then 0 else if n = 1 then i else
     -i * fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then f (n div d) * 
     dirichlet_inverse f i d + acc else acc) 1 (n - 1) 0)"
proof -
  consider "n = 0" | "n = 1" | "n > 1" by force
  thus ?thesis
  proof cases
    assume n: "n > 1"
    have *: "(\<lambda>d acc. if d dvd n then f (n div d) * dirichlet_inverse f i d + acc else acc) =
               (\<lambda>d acc. (if d dvd n then f (n div d) * dirichlet_inverse f i d else 0) + acc)"
      by (simp add: fun_eq_iff)
    have "fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then f (n div d) * 
            dirichlet_inverse f i d + acc else acc) 1 (n - 1) 0 = 
            (\<Sum>d = 1..n - 1. if d dvd n then f (n div d) * dirichlet_inverse f i d else 0)"
      by (subst *, subst sum_atLeastAtMost_code [symmetric]) simp
    also from n have "\<dots> = (\<Sum>d | d dvd n \<and> d < n. f (n div d) * dirichlet_inverse f i d)"
      by (intro sum.mono_neutral_cong_right; cases n)
         (auto dest: dvd_imp_le elim: dvdE simp: Suc_le_eq intro!: Nat.gr0I)
    also from n have "-i * \<dots> = dirichlet_inverse f i n"
      by (simp add: dirichlet_inverse_gt_1)
    finally show ?thesis using n by simp
  qed auto
qed
      
lemma dirichlet_prod_inverse:
  assumes "f 1 * i = 1"
  shows   "dirichlet_prod f (dirichlet_inverse f i) = (\<lambda>n. if n = 1 then 1 else 0)"
proof
  fix n :: nat
  consider "n = 0" | "n = 1" | "n > 1" by force
  thus "dirichlet_prod f (dirichlet_inverse f i) n = (if n = 1 then 1 else 0)"
  proof cases
    assume n: "n > 1"
    have fin: "finite {d. d dvd n \<and> d \<noteq> n}" 
      by (rule finite_subset[of _ "{d. d dvd n}"]) (insert n, auto)
    have "dirichlet_prod f (dirichlet_inverse f i) n = 
            (\<Sum>d | d dvd n. f (n div d) * dirichlet_inverse f i d)"
      by (simp add: dirichlet_prod_altdef1)
    also have "{d. d dvd n} = insert n {d. d dvd n \<and> d \<noteq> n}" by auto
    also have "(\<Sum>d\<in>\<dots>. f (n div d) * dirichlet_inverse f i d) = 
                 f 1 * dirichlet_inverse f i n + 
                 (\<Sum>d | d dvd n \<and> d \<noteq> n. f (n div d) * dirichlet_inverse f i d)"
      using fin n by (subst sum.insert) auto
    also from n have "dirichlet_inverse f i n = 
      - i * (\<Sum>d | d dvd n \<and> d < n. f (n div d) * dirichlet_inverse f i d)"
      by (subst dirichlet_inverse_gt_1) auto
    also from n have "{d. d dvd n \<and> d < n} = {d. d dvd n \<and> d \<noteq> n}" by (auto dest: dvd_imp_le)
    also have "f 1 * (- i * 
                   (\<Sum>d | d dvd n \<and> d \<noteq> n. f (n div d) * dirichlet_inverse f i d)) =
               -(f 1 * i) * 
                   (\<Sum>d | d dvd n \<and> d \<noteq> n. f (n div d) * dirichlet_inverse f i d)"
      by (simp add: mult.assoc)
    also have "f 1 * i = 1" by fact
    finally show ?thesis using n by simp
  qed (insert assms, simp_all add: dirichlet_prod_def)
qed
               
lemma dirichlet_prod_inverse':
  assumes "f 1 * i = 1"
  shows   "dirichlet_prod (dirichlet_inverse f i) f = (\<lambda>n. if n = 1 then 1 else 0)"
  using dirichlet_prod_inverse[of f] assms by (simp add: dirichlet_prod_commutes)

lemma dirichlet_inverse_noninvertible:
  assumes "f (Suc 0) = (0 :: 'a :: {comm_ring_1})" "i = 0"
  shows   "dirichlet_inverse f i n = 0"
  using assms
  by (induction f i n rule: dirichlet_inverse.induct) (auto simp: dirichlet_inverse.simps)

lemma multiplicative_dirichlet_prod:
  assumes "multiplicative_function f" 
  assumes "multiplicative_function g"
  shows   "multiplicative_function (dirichlet_prod f g)"
proof -
  interpret f: multiplicative_function f by fact
  interpret g: multiplicative_function g by fact
  show ?thesis
  proof
    fix a b :: nat assume "a > 1" "b > 1" and coprime: "coprime a b"
    hence "dirichlet_prod f g (a * b) = 
             (\<Sum>r | r dvd a. \<Sum>s | s dvd b. f (r * s) * g (a * b div (r * s)))"
      by (simp add: dirichlet_prod_def sum_divisors_coprime_mult)
    also have "\<dots> = (\<Sum>r | r dvd a. \<Sum>s | s dvd b. f r * f s * g (a div r) * g (b div s))"
    using \<open>coprime a b\<close> proof (rule sum_coprime_dvd_cong)
      fix r s
      assume "coprime r s" and "r dvd a" and "s dvd b"
      with \<open>a > 1\<close> \<open>b > 1\<close> have "r > 0" "s > 0"
        by (auto intro: ccontr)
      from \<open>coprime r s\<close> have "f (r * s) = f r * f s"
        by (rule f.mult_coprime)
      moreover from \<open>coprime a b\<close> have \<open>coprime (a div r) (b div s)\<close>
        using \<open>r > 0\<close> \<open>s > 0\<close> \<open>r dvd a\<close> \<open>s dvd b\<close> dvd_div_iff_mult [of r a] dvd_div_iff_mult [of s b]
        by (auto dest: coprime_imp_coprime dvd_mult_left)
      then have "g (a div r * (b div s)) = g (a div r) * g (b div s)"
        by (rule g.mult_coprime)
      ultimately show "f (r * s) * g (a * b div (r * s)) = f r * f s * g (a div r) * g (b div s)"
        using \<open>r dvd a\<close> \<open>s dvd b\<close> by (simp add: div_mult_div_if_dvd ac_simps)
    qed
    also have "\<dots> = dirichlet_prod f g a * dirichlet_prod f g b"
      unfolding dirichlet_prod_def by (simp add: sum_product mult_ac)
    finally show "dirichlet_prod f g (a * b) = \<dots>" .
  qed simp_all
qed
  
lemma multiplicative_dirichlet_prodD1:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_semiring_1_cancel"
  assumes "multiplicative_function (dirichlet_prod f g)"
  assumes "multiplicative_function f"
  assumes [simp]: "g 0 = 0"
  shows   "multiplicative_function g"
proof -
  interpret f: multiplicative_function f by fact
  interpret fg: multiplicative_function "dirichlet_prod f g" by fact
  show ?thesis
  proof
    have "dirichlet_prod f g (Suc 0) = 1" by (rule fg.Suc_0)
    also have "dirichlet_prod f g (Suc 0) = g 1" by (subst dirichlet_prod_Suc_0) simp
    finally show "g 1 = 1" by simp
  next
    fix a b :: nat assume ab: "a > 1" "b > 1" "coprime a b"
    hence "a > 0" "b > 0" "coprime a b" by simp_all
    thus "g (a * b) = g a * g b"
    proof (induction "a * b" arbitrary: a b rule: less_induct)
      case (less a b)
      have "dirichlet_prod f g (a * b) + g a * g b = 
              (\<Sum>r | r dvd a * b. f r * g (a * b div r)) + g a * g b"
        by (simp add: dirichlet_prod_def)
      also have "{r. r dvd a * b} = insert 1 {r. r dvd a * b \<and> r \<noteq> 1}" by auto
      also have "(\<Sum>r\<in>\<dots>. f r * g (a * b div r)) + g a * g b = 
                   g (a * b) + ((\<Sum>r | r dvd a * b \<and> r \<noteq> 1. f r * g (a * b div r)) + g a * g b)"
        using less.prems
        by (subst sum.insert) (auto intro!: finite_subset[OF _ finite_divisors_nat'] simp: add_ac)
      also have "(\<Sum>r | r dvd a * b \<and> r \<noteq> 1. f r * g (a * b div r)) = 
                     (\<Sum>r | r dvd a * b. if r = 1 then 0 else f r * g (a * b div r))"
        using less.prems by (intro sum.mono_neutral_cong_left) (auto intro: finite_divisors_nat')
      also have "\<dots> = (\<Sum>r | r dvd a. \<Sum>d | d dvd b.
                          if r * d = 1 then 0 else f (r * d) * g (a * b div (r * d)))"
        using \<open>coprime a b\<close> by (rule sum_divisors_coprime_mult)
      also have "\<dots> = (\<Sum>r | r dvd a. \<Sum>d | d dvd b.
                          if r * d = 1 then 0 else f (r * d) * g ((a div r) * (b div d)))"
        by (intro sum.cong refl) (auto elim!: dvdE)
      also have "\<dots> = (\<Sum>r | r dvd a. \<Sum>d | d dvd b.
                          if r * d = 1 then 0 else f r * f d * g (a div r) * g (b div d))"
      using \<open>coprime a b\<close> proof (rule sum_coprime_dvd_cong)
        fix r s
        assume "coprime r s" and "r dvd a" and "s dvd b"
        with \<open>a > 0\<close> \<open>b > 0\<close> have "r > 0" "s > 0"
          by (auto intro: ccontr)
        from \<open>coprime r s\<close> have f: "f (r * s) = f r * f s"
          by (rule f.mult_coprime)
        show "(if r * s = 1 then 0 else f (r * s) * g (a div r * (b div s))) =
          (if r * s = 1 then 0 else f r * f s * g (a div r) * g (b div s))"
        proof (cases "r * s = 1")
          case True
          then show ?thesis
            by simp
        next
          case False
          with \<open>r dvd a\<close> \<open>s dvd b\<close> less.prems
          have "(a div r) * (b div s) \<noteq> a * b"
            by (intro notI) (auto elim!: dvdE)
          moreover from \<open>r dvd a\<close> \<open>s dvd b\<close> less.prems
          have "(a div r) * (b div s) \<le> a * b" 
            by (intro dvd_imp_le mult_dvd_mono Nat.gr0I) (auto elim!: dvdE)
          ultimately have "(a div r) * (b div s) < a * b"
            by arith
          with \<open>r dvd a\<close> \<open>s dvd b\<close> less.prems
          have g: "g ((a div r) * (b div s)) = g (a div r) * g (b div s)"
            by (auto intro: less coprime_divisors [OF _ _ \<open>coprime a b\<close>] elim!: dvdE)
          from False show ?thesis
            by (auto simp: less f g ac_simps)
        qed
      qed
      also have "\<dots> = (\<Sum>(r,d)\<in>{r. r dvd a}\<times>{d. d dvd b}. 
                        if r * d = 1 then 0 else f r * f d * g (a div r) * g (b div d))"
        by (simp add: sum.cartesian_product)
      also have "\<dots> = (\<Sum>(r1,r2) \<in> {r1. r1 dvd a} \<times> {r2. r2 dvd b} - {(1,1)}.
                         (f r1 * f r2) * g (a div r1) * g (b div r2))" (is "_ = sum ?f ?A")
        using less.prems by (intro sum.mono_neutral_cong_right) (auto split: if_splits)
      also have "\<dots> + g a * g b = ?f (1, 1) + sum ?f ?A" by (simp add: add_ac)
      also have "\<dots> = sum ?f ({r1. r1 dvd a} \<times> {r2. r2 dvd b})" using less.prems
        by (intro sum.remove [symmetric]) auto
      also have "\<dots> = dirichlet_prod f g a * dirichlet_prod f g b"
        by (simp add: sum.cartesian_product sum_product dirichlet_prod_def mult_ac)
      also have "g (a * b) + dirichlet_prod f g a * dirichlet_prod f g b =
                   dirichlet_prod f g (a * b) + g (a * b)"
        using less.prems by (simp add: fg.mult_coprime add_ac)
      finally show ?case by simp
    qed
  qed simp_all
qed

lemma multiplicative_dirichlet_prodD2:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_semiring_1_cancel"
  assumes "multiplicative_function (dirichlet_prod f g)"
  assumes "multiplicative_function g"
  assumes [simp]: "f 0 = 0"
  shows   "multiplicative_function f"
proof -
  from assms(1) have "multiplicative_function (dirichlet_prod g f)"
    by (simp add: dirichlet_prod_commutes)
  from multiplicative_dirichlet_prodD1[OF this assms(2)] show ?thesis by simp
qed

lemma multiplicative_dirichlet_inverse:
  assumes "multiplicative_function f"
  shows   "multiplicative_function (dirichlet_inverse f 1)"
proof (rule multiplicative_dirichlet_prodD1[OF _ assms])
  interpret multiplicative_function f by fact
  have "multiplicative_function (\<lambda>n. if n = 1 then 1 else 0)"
    by standard simp_all
  thus "multiplicative_function (dirichlet_prod f (dirichlet_inverse f 1))"
    by (subst dirichlet_prod_inverse) simp_all
qed simp_all
  
lemma dirichlet_prod_prime_power:
  assumes "prime p"
  shows   "dirichlet_prod f g (p ^ k) = (\<Sum>i\<le>k. f (p ^ i) * g (p ^ (k - i)))"
proof -
  have "dirichlet_prod f g (p ^ k) = (\<Sum>i\<le>k. f (p ^ i) * g (p ^ k div p ^ i))"
    unfolding dirichlet_prod_def using assms
    by (intro sum.reindex_bij_betw [symmetric] bij_betw_prime_power_divisors)
  also from assms have "\<dots> = (\<Sum>i\<le>k. f (p ^ i) * g (p ^ (k - i)))"
    by (intro sum.cong refl) (auto simp: power_diff')
  finally show ?thesis .
qed

lemma dirichlet_prod_prime:
  assumes "prime p"
  shows   "dirichlet_prod f g p  = f 1 * g p + f p * g 1"
  using dirichlet_prod_prime_power[of p f g 1] assms by simp
    
locale multiplicative_dirichlet_prod = 
  f: multiplicative_function f + g: multiplicative_function g 
  for f g :: "nat \<Rightarrow> 'a :: comm_semiring_1"
begin

sublocale multiplicative_function "dirichlet_prod f g"
  by (intro multiplicative_dirichlet_prod 
        f.multiplicative_function_axioms g.multiplicative_function_axioms)

end
  
locale multiplicative_dirichlet_prod' = 
  f: multiplicative_function' f f_prime_power f_prime + 
  g: multiplicative_function' g g_prime_power g_prime
  for f g :: "nat \<Rightarrow> 'a :: comm_semiring_1" and f_prime_power g_prime_power f_prime g_prime
begin
  
sublocale multiplicative_dirichlet_prod f g ..

sublocale multiplicative_function' "dirichlet_prod f g" 
  "\<lambda>p k. f_prime_power p k + g_prime_power p k + 
      (\<Sum>i\<in>{0<..<k}. f_prime_power p i * g_prime_power p (k - i))" 
  "\<lambda>p. f_prime p + g_prime p"
proof (standard, goal_cases)
  case (1 p k)
  hence "dirichlet_prod f g (p ^ k) = (\<Sum>i\<le>k. f (p ^ i) * g (p ^ (k - i)))"
    by (intro dirichlet_prod_prime_power)
  also from 1 have "{..k} = insert 0 (insert k {0<..<k})" by auto
  also have "(\<Sum>i\<in>\<dots>. f (p ^ i) * g (p ^ (k - i))) = 
               f_prime_power p k + g_prime_power p k + 
               (\<Sum>i\<in>{0<..<k}. f (p ^ i) * g (p ^ (k - i)))" using 1
    by (auto simp: f.prime_power g.prime_power add_ac)
  also have "(\<Sum>i\<in>{0<..<k}. f (p ^ i) * g (p ^ (k - i))) = 
               (\<Sum>i\<in>{0<..<k}. f_prime_power p i * g_prime_power p (k - i))"
    using 1 by (intro sum.cong) (auto simp: f.prime_power g.prime_power)
  finally show ?case .
next
  case (2 p)
  have "{0<..<Suc 0} = {}" by auto
  with 2 show ?case
    by (auto simp: f.prime_power [symmetric] g.prime_power [symmetric] f.prime g.prime add_ac)
qed
    
end

end
