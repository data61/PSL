(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Missing lemmas\<close>

text \<open>This theory contains many results that are important but not specific for our development. 
      They could be moved to the stardard library and some other AFP entries.\<close> 

theory Missing_Lemmas
  imports
    Berlekamp_Zassenhaus.Sublist_Iteration (* for thm upt_append *)
    Berlekamp_Zassenhaus.Square_Free_Int_To_Square_Free_GFp (* for thm large_mod_0 *)
    Algebraic_Numbers.Resultant
    Jordan_Normal_Form.Conjugate
    Jordan_Normal_Form.Missing_VectorSpace
    Jordan_Normal_Form.VS_Connect
    Berlekamp_Zassenhaus.Finite_Field_Factorization_Record_Based (* for transfer rules for thm vec_of_list_Nil *)
    Berlekamp_Zassenhaus.Berlekamp_Hensel (* for unique_factorization_m_factor *)
begin

no_notation test_bit (infixl "!!" 100)

hide_const(open) module.smult up_ring.monom up_ring.coeff

(**** Could be merged to HOL/Rings.thy ****)

lemma (in zero_less_one) zero_le_one [simp]: "0 \<le> 1" by (rule less_imp_le, simp)
subclass (in zero_less_one) zero_neq_one by (unfold_locales, simp add: less_imp_neq)

class ordered_semiring_1 = Rings.ordered_semiring_0 + monoid_mult + zero_less_one
begin

subclass semiring_1..

lemma of_nat_ge_zero[intro!]: "of_nat n \<ge> 0"
  using add_right_mono[of _ _ 1] by (induct n, auto)

(* Following lemmas are moved from @{class ordered_idom}. *)
lemma zero_le_power [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> a ^ n"
  by (induct n) simp_all

lemma power_mono: "a \<le> b \<Longrightarrow> 0 \<le> a \<Longrightarrow> a ^ n \<le> b ^ n"
  by (induct n) (auto intro: mult_mono order_trans [of 0 a b])

lemma one_le_power [simp]: "1 \<le> a \<Longrightarrow> 1 \<le> a ^ n"
  using power_mono [of 1 a n] by simp

lemma power_le_one: "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ n \<le> 1"
  using power_mono [of a 1 n] by simp

lemma power_gt1_lemma:
  assumes gt1: "1 < a"
  shows "1 < a * a ^ n"
proof -
  from gt1 have "0 \<le> a"
    by (fact order_trans [OF zero_le_one less_imp_le])
  from gt1 have "1 * 1 < a * 1" by simp
  also from gt1 have "\<dots> \<le> a * a ^ n"
    by (simp only: mult_mono \<open>0 \<le> a\<close> one_le_power order_less_imp_le zero_le_one order_refl)
  finally show ?thesis by simp
qed

lemma power_gt1: "1 < a \<Longrightarrow> 1 < a ^ Suc n"
  by (simp add: power_gt1_lemma)

lemma one_less_power [simp]: "1 < a \<Longrightarrow> 0 < n \<Longrightarrow> 1 < a ^ n"
  by (cases n) (simp_all add: power_gt1_lemma)

lemma power_decreasing: "n \<le> N \<Longrightarrow> 0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ N \<le> a ^ n"
proof (induction N)
  case (Suc N)
  then have "a * a^N \<le> 1 * a^n" if "n \<le> N"
    using that by (intro mult_mono) auto
  then show ?case
    using Suc by (auto simp add: le_Suc_eq)
qed (auto)

lemma power_increasing: "n \<le> N \<Longrightarrow> 1 \<le> a \<Longrightarrow> a ^ n \<le> a ^ N"
proof (induction N)
  case (Suc N)
  then have "1 * a^n \<le> a * a^N" if "n \<le> N"
    using that by (intro mult_mono) (auto simp add: order_trans[OF zero_le_one])
  then show ?case
    using Suc by (auto simp add: le_Suc_eq)
qed (auto)

lemma power_Suc_le_self: "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ Suc n \<le> a"
  using power_decreasing [of 1 "Suc n" a] by simp

end

lemma prod_list_nonneg: "(\<And> x. (x :: 'a :: ordered_semiring_1) \<in> set xs \<Longrightarrow> x \<ge> 0) \<Longrightarrow> prod_list xs \<ge> 0"
  by (induct xs, auto)

subclass (in ordered_idom) ordered_semiring_1 by unfold_locales auto

(**** End of lemmas that could be moved to HOL/Rings.thy ****)

(* missing lemma on logarithms *)
lemma log_prod: assumes "0 < a" "a \<noteq> 1" "\<And> x. x \<in> X \<Longrightarrow> 0 < f x" 
  shows "log a (prod f X) = sum (log a o f) X" 
  using assms(3)
proof (induct X rule: infinite_finite_induct)
  case (insert x F)
  have "log a (prod f (insert x F)) = log a (f x * prod f F)" using insert by simp
  also have "\<dots> = log a (f x) + log a (prod f F)" 
    by (rule log_mult[OF assms(1-2) insert(4) prod_pos], insert insert, auto)
  finally show ?case using insert by auto
qed auto

(* TODO: Jordan_Normal_Form/Missing_Ring.ordered_idom should be redefined *)
subclass (in ordered_idom) zero_less_one by (unfold_locales, auto)
hide_fact Missing_Ring.zero_less_one

(**** The following lemmas could be part of the standard library ****)

instance real :: ordered_semiring_strict by (intro_classes, auto)
instance real :: linordered_idom..

(*This is a generalisation of thm less_1_mult*) 
lemma less_1_mult': 
  fixes a::"'a::linordered_semidom"
  shows "1 < a \<Longrightarrow> 1 \<le> b \<Longrightarrow> 1 < a * b"
  by (metis le_less less_1_mult mult.right_neutral)

lemma upt_minus_eq_append: "i\<le>j \<Longrightarrow> i\<le>j-k \<Longrightarrow> [i..<j] = [i..<j-k] @ [j-k..<j]"
proof (induct k)
  case (Suc k)
  have hyp: "[i..<j] = [i..<j - k] @ [j - k..<j]" using Suc.hyps Suc.prems by auto
  then show ?case
    by (metis Suc.prems(2) append.simps(1) diff_Suc_less nat_less_le neq0_conv upt_append upt_rec zero_diff)
qed auto

lemma list_trisect: "x < length lst \<Longrightarrow> [0..<length lst] = [0..<x]@x#[Suc x..<length lst]"
  by (induct lst, force, rename_tac a lst, case_tac "x = length lst", auto)

lemma id_imp_bij_betw:
  assumes f: "f : A \<rightarrow> A"
      and ff: "\<And>a. a \<in> A \<Longrightarrow> f (f a) = a"
  shows "bij_betw f A A"
  by (intro bij_betwI[OF f f], simp_all add: ff)

lemma range_subsetI:
  assumes "\<And>x. f x = g (h x)" shows "range f \<subseteq> range g"
  using assms by auto

lemma Gcd_uminus: 
  fixes A::"int set"
  assumes "finite A"
  shows "Gcd A = Gcd (uminus ` A)"
  using assms
  by (induct A, auto)

lemma aux_abs_int: fixes c :: int
  assumes "c \<noteq> 0" 
  shows "\<bar>x\<bar> \<le> \<bar>x * c\<bar>"
proof -
  have "abs x = abs x * 1" by simp
  also have "\<dots> \<le> abs x * abs c" 
    by (rule mult_left_mono, insert assms, auto)
  finally show ?thesis unfolding abs_mult by auto
qed

lemma mod_0_abs_less_imp_0:
  fixes a::int
  assumes a1: "[a = 0] (mod m)"
  and a2: "abs(a)<m"
  shows "a = 0"
proof -
  have "m\<ge>0" using assms by auto
  thus ?thesis  
    using assms unfolding cong_def
    using int_mod_pos_eq large_mod_0 zless_imp_add1_zle 
      by (metis abs_of_nonneg le_less not_less zabs_less_one_iff zmod_trival_iff)
qed

(* an intro version of sum_list_0 *)
lemma sum_list_zero:
  assumes "set xs \<subseteq> {0}" shows "sum_list xs = 0"
  using assms by (induct xs, auto)

(* About @{const max} *)
lemma max_idem [simp]: shows "max a a = a" by (simp add: max_def)

lemma hom_max:
  assumes "a \<le> b \<longleftrightarrow> f a \<le> f b"
  shows "f (max a b) = max (f a) (f b)" using assms by (auto simp: max_def)

lemma le_max_self:
  fixes a b :: "'a :: preorder"
  assumes "a \<le> b \<or> b \<le> a" shows "a \<le> max a b" and "b \<le> max a b"
  using assms by (auto simp: max_def)

lemma le_max:
  fixes a b :: "'a :: preorder"
  assumes "c \<le> a \<or> c \<le> b" and "a \<le> b \<or> b \<le> a" shows "c \<le> max a b"
  using assms(1) le_max_self[OF assms(2)] by (auto dest: order_trans)

fun max_list where
  "max_list [] = (THE x. False)" (* more convenient than "undefined" *)
| "max_list [x] = x"
| "max_list (x # y # xs) = max x (max_list (y # xs))"

declare max_list.simps(1) [simp del]
declare max_list.simps(2-3)[code]

lemma max_list_Cons: "max_list (x#xs) = (if xs = [] then x else max x (max_list xs))"
  by (cases xs, auto)

lemma max_list_mem: "xs \<noteq> [] \<Longrightarrow> max_list xs \<in> set xs"
  by (induct xs, auto simp: max_list_Cons max_def)

lemma mem_set_imp_le_max_list:
  fixes xs :: "'a :: preorder list"
  assumes "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<le> b \<or> b \<le> a"
      and "a \<in> set xs"
  shows "a \<le> max_list xs"
proof (insert assms, induct xs arbitrary:a)
  case Nil
  with assms show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case False
    have "x \<le> max_list xs \<or> max_list xs \<le> x"
      apply (rule Cons(2)) using max_list_mem[of xs] False by auto
    note 1 = le_max_self[OF this]
    from Cons have "a = x \<or> a \<in> set xs" by auto
    then show ?thesis
    proof (elim disjE)
      assume a: "a = x"
      show ?thesis by (unfold a max_list_Cons, auto simp: False intro!: 1)
    next
      assume "a \<in> set xs"
      then have "a \<le> max_list xs" by (intro Cons, auto)
      with 1 have "a \<le> max x (max_list xs)" by (auto dest: order_trans)
      then show ?thesis by (unfold max_list_Cons, auto simp: False)
    qed
  qed (insert Cons, auto)
qed

lemma le_max_list:
  fixes xs :: "'a :: preorder list"
  assumes ord: "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<le> b \<or> b \<le> a"
      and ab: "a \<le> b"
      and b: "b \<in> set xs"
  shows "a \<le> max_list xs"
proof-
  note ab
  also have "b \<le> max_list xs"
    by (rule mem_set_imp_le_max_list, fact ord, fact b)
  finally show ?thesis.
qed

lemma max_list_le:
  fixes xs :: "'a :: preorder list"
  assumes a: "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> a"
      and xs: "xs \<noteq> []"
  shows "max_list xs \<le> a"
  using max_list_mem[OF xs] a by auto

lemma max_list_as_Greatest:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<le> y \<or> y \<le> x"
  shows "max_list xs = (GREATEST a. a \<in> set xs)"
proof (cases "xs = []")
  case True
  then show ?thesis by (unfold Greatest_def, auto simp: max_list.simps(1))
next
  case False
  from assms have 1: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs" for x
    by (auto intro: le_max_list)
  have 2: "max_list xs \<in> set xs" by (fact max_list_mem[OF False])
  have "\<exists>!x. x \<in> set xs \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y \<le> x)" (is "\<exists>!x. ?P x")
  proof (intro ex1I)
    from 1 2
    show "?P (max_list xs)" by auto
  next
    fix x assume 3: "?P x"
    with 1 have "x \<le> max_list xs" by auto
    moreover from 2 3 have "max_list xs \<le> x" by auto
    ultimately show "x = max_list xs" by auto
  qed
  note 3 = theI_unique[OF this,symmetric]
  from 1 2 show ?thesis
    by (unfold Greatest_def Cons 3, auto)
qed

lemma hom_max_list_commute:
  assumes "xs \<noteq> []"
      and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> h (max x y) = max (h x) (h y)"
  shows "h (max_list xs) = max_list (map h xs)"
  by (insert assms, induct xs, auto simp: max_list_Cons max_list_mem)


(*Efficient rev [i..<j]*)
primrec rev_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" ("(1[_>.._])") where
rev_upt_0: "[0>..j] = []" |
rev_upt_Suc: "[(Suc i)>..j] = (if i \<ge> j then i # [i>..j] else [])"

lemma rev_upt_rec: "[i>..j] = (if i>j then [i>..Suc j] @ [j] else [])"
  by (induct i, auto)    

definition rev_upt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "rev_upt_aux i j js = [i>..j] @ js"

lemma upt_aux_rec [code]:
  "rev_upt_aux i j js = (if j\<ge>i then js else rev_upt_aux i (Suc j) (j#js))"
  by (induct j, auto simp add: rev_upt_aux_def rev_upt_rec)

lemma rev_upt_code[code]: "[i>..j] = rev_upt_aux i j []"
  by(simp add: rev_upt_aux_def)    
  
lemma upt_rev_upt:
  "rev [j>..i] = [i..<j]"
  by (induct j, auto)
    
lemma rev_upt_upt:
  "rev [i..<j] = [j>..i]"
  by (induct j, auto) 

lemma length_rev_upt [simp]: "length [i>..j] = i - j"
  by (induct i) (auto simp add: Suc_diff_le)
    
lemma nth_rev_upt [simp]: "j + k < i \<Longrightarrow> [i>..j] ! k = i - 1 - k"
proof -
  assume jk_i: "j + k < i"
  have "[i>..j] = rev [j..<i]" using rev_upt_upt by simp
  also have "... ! k = [j..<i] ! (length [j..<i] - 1 - k)"
    by (rule nth_rev, insert jk_i, auto)
  also have "... = [j..<i] ! (i - j - 1 - k)" by auto
  also have "... = j + (i - j - 1 - k)" by (rule nth_upt, insert jk_i, auto)
  finally show ?thesis using jk_i by auto
qed    
  
lemma nth_map_rev_upt: 
  assumes i: "i < m-n"
  shows "(map f [m>..n]) ! i = f (m - 1 - i)"
proof -
  have "(map f [m>..n]) ! i = f ([m>..n] ! i)" by (rule nth_map, auto simp add: i)
  also have "... = f (m - 1 - i)"
  proof (rule arg_cong[of _ _ f], rule nth_rev_upt)
    show "n + i < m" using i by linarith
  qed
  finally show ?thesis .
qed

lemma coeff_mult_monom:
 "coeff (p * monom a d) i = (if d \<le> i then a * coeff p (i - d) else 0)"
  using coeff_monom_mult[of a d p] by (simp add: ac_simps)

(**** End of the lemmas which may be part of the standard library ****)

(**** The following lemmas could be moved to Algebraic_Numbers/Resultant.thy ****)
lemma vec_of_poly_0 [simp]: "vec_of_poly 0 = 0\<^sub>v 1" by (auto simp: vec_of_poly_def)

lemma vec_index_vec_of_poly [simp]: "i \<le> degree p \<Longrightarrow> vec_of_poly p $ i = coeff p (degree p - i)"
  by (simp add: vec_of_poly_def Let_def)

lemma poly_of_vec_vec: "poly_of_vec (vec n f) = Poly (rev (map f [0..<n]))"
proof (induct n arbitrary:f)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "map f [0..<Suc n] = f 0 # map (f \<circ> Suc) [0..<n]" by (simp add: map_upt_Suc del: upt_Suc)
  also have "Poly (rev \<dots>) = Poly (rev (map (f \<circ> Suc) [0..<n])) + monom (f 0) n"
    by (simp add: Poly_snoc smult_monom)
  also have "\<dots> = poly_of_vec (vec n (f \<circ> Suc)) + monom (f 0) n"
    by (fold Suc, simp)
  also have "\<dots> = poly_of_vec (vec (Suc n) f)"
    apply (unfold poly_of_vec_def Let_def dim_vec sum.lessThan_Suc)
    by (auto simp add: Suc_diff_Suc)
  finally show ?case..
qed

lemma sum_list_map_dropWhile0:
  assumes f0: "f 0 = 0"
  shows "sum_list (map f (dropWhile ((=) 0) xs)) = sum_list (map f xs)"
  by (induct xs, auto simp add: f0)

lemma coeffs_poly_of_vec:
  "coeffs (poly_of_vec v) = rev (dropWhile ((=) 0) (list_of_vec v))"
proof-
  obtain n f where v: "v = vec n f" by transfer auto
  show ?thesis by (simp add: v poly_of_vec_vec)
qed

lemma poly_of_vec_vCons:
 "poly_of_vec (vCons a v) = monom a (dim_vec v) + poly_of_vec v" (is "?l = ?r")
  by (auto intro: poly_eqI simp: coeff_poly_of_vec vec_index_vCons)

lemma poly_of_vec_as_Poly: "poly_of_vec v = Poly (rev (list_of_vec v))"
  by (induct v, auto simp:poly_of_vec_vCons Poly_snoc ac_simps)

lemma poly_of_vec_add:
  assumes "dim_vec a = dim_vec b"
  shows "poly_of_vec (a + b) = poly_of_vec a + poly_of_vec b"
  using assms
  by (auto simp add: poly_eq_iff coeff_poly_of_vec)

(*TODO: replace the one in Resultant.thy*)
lemma degree_poly_of_vec_less:
  assumes "0 < dim_vec v" and "dim_vec v \<le> n" shows "degree (poly_of_vec v) < n"
  using degree_poly_of_vec_less assms by (auto dest: less_le_trans)

lemma (in vec_module) poly_of_vec_finsum:
  assumes "f \<in> X \<rightarrow> carrier_vec n"
  shows "poly_of_vec (finsum V f X) = (\<Sum>i\<in>X. poly_of_vec (f i))"
proof (cases "finite X")
  case False then show ?thesis by auto
next
  case True show ?thesis
  proof (insert True assms, induct X rule: finite_induct)
    case IH: (insert a X)
    have [simp]: "f x \<in> carrier_vec n" if x: "x \<in> X" for x 
      using x IH.prems unfolding Pi_def by auto
    have [simp]: "f a \<in> carrier_vec n" using IH.prems unfolding Pi_def by auto
    have [simp]: "dim_vec (finsum V f X) = n" by simp
    have [simp]: "dim_vec (f a) = n" by simp
    show ?case
    proof (cases "a \<in> X")
      case True then show ?thesis by (auto simp: insert_absorb IH)
    next
      case False
      then have "(finsum V f (insert a X)) = f a + (finsum V f X)" 
        by (auto intro: finsum_insert IH)
      also have "poly_of_vec ... = poly_of_vec (f a) + poly_of_vec (finsum V f X)"
        by (rule poly_of_vec_add, simp)
      also have "... = (\<Sum>i\<in>insert a X. poly_of_vec (f i))"
        using IH False by (subst sum.insert, auto)
      finally show ?thesis .
    qed
  qed auto
qed

(*This function transforms a polynomial to a vector of dimension n*)  
definition "vec_of_poly_n p n =
  vec n (\<lambda>i. if i < n - degree p - 1 then 0 else coeff p (n - i - 1))"

(* TODO: make it abbreviation? *)
lemma vec_of_poly_as: "vec_of_poly_n p (Suc (degree p)) = vec_of_poly p"
  by (induct p, auto simp: vec_of_poly_def vec_of_poly_n_def)

lemma vec_of_poly_n_0 [simp]: "vec_of_poly_n p 0 = vNil"
  by (auto simp: vec_of_poly_n_def)

lemma vec_dim_vec_of_poly_n [simp]:
  "dim_vec (vec_of_poly_n p n) = n"
  "vec_of_poly_n p n \<in> carrier_vec n"
  unfolding vec_of_poly_n_def by auto

lemma dim_vec_of_poly [simp]: "dim_vec (vec_of_poly f) = degree f + 1"
  by (simp add: vec_of_poly_as[symmetric])

lemma vec_index_of_poly_n:
  assumes "i < n"
  shows "vec_of_poly_n p n $ i =
    (if i < n - Suc (degree p) then 0 else coeff p (n - i - 1))"
  using assms by (auto simp: vec_of_poly_n_def Let_def)

lemma vec_of_poly_n_pCons[simp]:
  shows "vec_of_poly_n (pCons a p) (Suc n) = vec_of_poly_n p n @\<^sub>v vec_of_list [a]" (is "?l = ?r")
proof (unfold vec_eq_iff, intro conjI allI impI)
  show "dim_vec ?l = dim_vec ?r" by auto
  show "i < dim_vec ?r \<Longrightarrow> ?l $ i = ?r $ i" for i
    by (cases "n - i", auto simp: coeff_pCons less_Suc_eq_le vec_index_of_poly_n)
qed

lemma vec_of_poly_pCons:
  shows "vec_of_poly (pCons a p) =
   (if p = 0 then vec_of_list [a] else vec_of_poly p @\<^sub>v vec_of_list [a])"
  by (cases "degree p", auto simp: vec_of_poly_as[symmetric])

lemma list_of_vec_of_poly [simp]:
  "list_of_vec (vec_of_poly p) = (if p = 0 then [0] else rev (coeffs p))"
  by (induct p, auto simp: vec_of_poly_pCons)

lemma poly_of_vec_of_poly_n:
  assumes p: "degree p<n"
  shows "poly_of_vec (vec_of_poly_n p n) = p"
proof - 
  have "vec_of_poly_n p n $ (n - Suc i) = coeff p i" if i: "i < n" for i    
  proof -
    have n: "n - Suc i < n" using i by auto
    have "vec_of_poly_n p n $ (n - Suc i) = 
      (if n - Suc i < n - Suc (degree p) then 0 else coeff p (n - (n - Suc i) - 1))"
      using vec_index_of_poly_n[OF n, of p] .
    also have "... = coeff p i" using i n le_degree by fastforce
    finally show ?thesis .
  qed
  moreover have "coeff p i = 0" if i2: "i \<ge> n" for i
    by (rule coeff_eq_0, insert i2 p, simp)
  ultimately show ?thesis
  using assms
  unfolding poly_eq_iff
  unfolding coeff_poly_of_vec by auto
qed

lemma vec_of_poly_n0[simp]: "vec_of_poly_n 0 n = 0\<^sub>v n" 
  unfolding vec_of_poly_n_def by auto

lemma vec_of_poly_n_add: "vec_of_poly_n (a + b) n = vec_of_poly_n a n + vec_of_poly_n b n"
proof (induct n arbitrary: a b)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by (cases a, cases b, auto)
qed

lemma vec_of_poly_n_poly_of_vec:
  assumes n: "dim_vec g = n"
  shows "vec_of_poly_n (poly_of_vec g) n = g"
proof (auto simp add: poly_of_vec_def vec_of_poly_n_def assms vec_eq_iff Let_def)
  have d: "degree (\<Sum>i<n. monom (g $ (n - Suc i)) i) = degree (poly_of_vec g)" 
    unfolding poly_of_vec_def Let_def n by auto
  fix i assume i1: "i < n - Suc (degree (\<Sum>i<n. monom (g $ (n - Suc i)) i))" 
    and i2: "i < n"
  have i3: "i < n - Suc (degree (poly_of_vec g))" 
    using i1 unfolding d by auto
  hence "dim_vec g - Suc i > degree (poly_of_vec g)"
    using n by linarith
  then show "g $ i = 0" using i1 i2 i3    
    by (metis (no_types, lifting) Suc_diff_Suc coeff_poly_of_vec diff_Suc_less 
        diff_diff_cancel leD le_degree less_imp_le_nat n neq0_conv)
next
  fix i assume "i < n"
  thus "coeff (\<Sum>i<n. monom (g $ (n - Suc i)) i) (n - Suc i) = g $ i"    
    by (metis (no_types) Suc_diff_Suc coeff_poly_of_vec diff_diff_cancel 
        diff_less_Suc less_imp_le_nat n not_less_eq poly_of_vec_def)
qed

lemma poly_of_vec_scalar_mult:
  assumes "degree b<n"
  shows "poly_of_vec (a \<cdot>\<^sub>v (vec_of_poly_n b n)) = smult a b"
  using assms
  by (auto simp add: poly_eq_iff coeff_poly_of_vec vec_of_poly_n_def coeff_eq_0)

(*TODO: replace the one in Resultant.thy*)
definition vec_of_poly_rev_shifted where
  "vec_of_poly_rev_shifted p n s j \<equiv>
   vec n (\<lambda>i. if i \<le> j \<and> j \<le> s + i then coeff p (s + i - j) else 0)"

lemma vec_of_poly_rev_shifted_dim[simp]: "dim_vec (vec_of_poly_rev_shifted p n s j) = n"
  unfolding vec_of_poly_rev_shifted_def by auto

lemma col_sylvester_sub: (* TODO: from this directly derive col_sylvester *)
  assumes j: "j < m + n"
  shows "col (sylvester_mat_sub m n p q) j =
    vec_of_poly_rev_shifted p n m j @\<^sub>v vec_of_poly_rev_shifted q m n j" (is "?l = ?r")
proof
  show "dim_vec ?l = dim_vec ?r" by simp
  fix i assume "i < dim_vec ?r" then have i: "i < m+n" by auto
  show "?l $ i = ?r $ i"
    unfolding vec_of_poly_rev_shifted_def
    apply (subst index_col) using i apply simp using j apply simp
    apply (subst sylvester_mat_sub_index) using i apply simp using j apply simp
    apply (cases "i < n") using i apply force using i
    apply (auto simp: not_less not_le intro!: coeff_eq_0)
    done
qed

lemma vec_of_poly_rev_shifted_scalar_prod:
  fixes p v
  defines "q \<equiv> poly_of_vec v"
  assumes m: "degree p \<le> m" and n: "dim_vec v = n"
  assumes j: "j < m+n"
  shows "vec_of_poly_rev_shifted p n m (n+m-Suc j) \<bullet> v = coeff (p * q) j" (is "?l = ?r")
proof -
  have id1: "\<And> i. m + i - (n + m - Suc j) = i + Suc j - n"
    using j by auto
  let ?g = "\<lambda> i. if i \<le> n + m - Suc j \<and> n - Suc j \<le> i then coeff p (i + Suc j - n) *  v $ i else 0"
  have "?thesis = ((\<Sum>i = 0..<n. ?g i) =          
        (\<Sum>i\<le>j. coeff p i * (if j - i < n then v $ (n - Suc (j - i)) else 0)))" (is "_ = (?l = ?r)")
    unfolding vec_of_poly_rev_shifted_def coeff_mult m scalar_prod_def n q_def
      coeff_poly_of_vec 
    by (subst sum.cong, insert id1, auto)
  also have "..." 
  proof -
    have "?r = (\<Sum>i\<le>j. (if j - i < n then coeff p i * v $ (n - Suc (j - i)) else 0))" (is "_ = sum ?f _")
      by (rule sum.cong, auto)
    also have "sum ?f {..j} = sum ?f ({i. i \<le> j \<and> j - i < n} \<union> {i. i \<le> j \<and> \<not> j - i < n})" 
      (is "_ = sum _ (?R1 \<union> ?R2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?f ?R1 + sum ?f ?R2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?f ?R2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?f ?R1 + 0 = sum (\<lambda> i. coeff p i * v $ (i + n - Suc j)) ?R1"
      (is "_ = sum ?F _")
      by (subst sum.cong, auto simp: ac_simps)
    also have "\<dots> = sum ?F ((?R1 \<inter> {..m}) \<union> (?R1 - {..m}))"
      (is "_ = sum _ (?R \<union> ?R')")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?F ?R + sum ?F ?R'"
      by (subst sum.union_disjoint, auto)
    also have "sum ?F ?R' = 0"
    proof -
      { 
        fix x
        assume "x > m" 
        with m
        have "?F x = 0" by (subst coeff_eq_0, auto)
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have r: "?r = sum ?F ?R" by simp

    have "?l = sum ?g ({i. i < n \<and> i \<le> n + m - Suc j \<and> n - Suc j \<le> i} 
      \<union> {i. i < n \<and> \<not> (i \<le> n + m - Suc j \<and> n - Suc j \<le> i)})" 
      (is "_ = sum _ (?L1 \<union> ?L2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?g ?L1 + sum ?g ?L2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?g ?L2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?g ?L1 + 0 = sum (\<lambda> i. coeff p (i + Suc j - n) * v $ i) ?L1"
      (is "_ = sum ?G _")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G (?L1 \<inter> {i. i + Suc j - n \<le> m} \<union> (?L1 - {i. i + Suc j - n \<le> m}))"
      (is "_ = sum _ (?L \<union> ?L')")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G ?L + sum ?G ?L'"
      by (subst sum.union_disjoint, auto)
    also have "sum ?G ?L' = 0"
    proof -
      {
        fix x
        assume "x + Suc j - n > m" 
        with m
        have "?G x = 0" by (subst coeff_eq_0, auto)
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have l: "?l = sum ?G ?L" by simp

    let ?bij = "\<lambda> i. i + n - Suc j"
    {
      fix x
      assume x: "j < m + n" "Suc (x + j) - n \<le> m" "x < n" "n - Suc j \<le> x" 
      define y where "y = x + Suc j - n"
      from x have "x + Suc j \<ge> n" by auto
      with x have xy: "x = ?bij y" unfolding y_def by auto
      from x have y: "y \<in> ?R" unfolding y_def by auto
      have "x \<in> ?bij ` ?R" unfolding xy using y by blast
    } note tedious = this
    show ?thesis unfolding l r
      by (rule sum.reindex_cong[of ?bij], insert j, auto simp: inj_on_def tedious)
  qed
  finally show ?thesis by simp
qed

lemma sylvester_sub_poly:
  fixes p q :: "'a :: comm_semiring_0 poly"
  assumes m: "degree p \<le> m"
  assumes n: "degree q \<le> n"
  assumes v: "v \<in> carrier_vec (m+n)"
  shows "poly_of_vec ((sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v) =
    poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q" (is "?l = ?r")
proof (rule poly_eqI)
  fix i
  let ?Tv = "(sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v"
  have dim: "dim_vec (vec_first v n) = n" "dim_vec (vec_last v m) = m" "dim_vec ?Tv = n + m" 
    using v by auto
  have if_distrib: "\<And> x y z. (if x then y else (0 :: 'a)) * z = (if x then y * z else 0)" 
    by auto
  show "coeff ?l i = coeff ?r i"
  proof (cases "i < m+n")
    case False
      hence i_mn: "i \<ge> m+n"
        and i_n: "\<And>x. x \<le> i \<and> x < n \<longleftrightarrow> x < n"
        and i_m: "\<And>x. x \<le> i \<and> x < m \<longleftrightarrow> x < m" by auto
      have "coeff ?r i =
            (\<Sum> x < n. vec_first v n $ (n - Suc x) * coeff p (i - x)) +
            (\<Sum> x < m. vec_last v m $ (m - Suc x) * coeff q (i - x))"
        (is "_ = sum ?f _ + sum ?g _")
        unfolding coeff_add coeff_mult Let_def 
        unfolding coeff_poly_of_vec dim if_distrib
        unfolding atMost_def
        apply(subst sum.inter_filter[symmetric],simp)
        apply(subst sum.inter_filter[symmetric],simp)
        unfolding mem_Collect_eq
        unfolding i_n i_m
        unfolding lessThan_def by simp
      also { fix x assume x: "x < n"
        have "coeff p (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x m by auto
        hence "?f x = 0" by auto
      } hence "sum ?f {..<n} = 0" by auto
      also { fix x assume x: "x < m"
        have "coeff q (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x n by auto
        hence "?g x = 0" by auto
      } hence "sum ?g {..<m} = 0" by auto
      finally have "coeff ?r i = 0" by auto
      also from False have "0 = coeff ?l i"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      finally show ?thesis by auto
    next case True
      hence "coeff ?l i = ((sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v) $ (n + m - Suc i)"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      also have "... = coeff (p * poly_of_vec (vec_first v n) + q * poly_of_vec (vec_last v m)) i"
        apply(subst index_mult_mat_vec) using True apply simp
        apply(subst row_transpose) using True apply simp
        apply(subst col_sylvester_sub)
        using True apply simp
        apply(subst vec_first_last_append[of v n m,symmetric]) using v apply(simp add: add.commute)
        apply(subst scalar_prod_append)
        apply (rule carrier_vecI,simp)+
        apply (subst vec_of_poly_rev_shifted_scalar_prod[OF m],simp) using True apply simp
        apply (subst add.commute[of n m])
        apply (subst vec_of_poly_rev_shifted_scalar_prod[OF n]) apply simp using True apply simp
        by simp
      also have "... =
        (\<Sum>x\<le>i. (if x < n then vec_first v n $ (n - Suc x) else 0) * coeff p (i - x)) +
        (\<Sum>x\<le>i. (if x < m then vec_last v m $ (m - Suc x) else 0) * coeff q (i - x))"
        unfolding coeff_poly_of_vec[of "vec_first v n",unfolded dim_vec_first,symmetric]
        unfolding coeff_poly_of_vec[of "vec_last v m",unfolded dim_vec_last,symmetric]
        unfolding coeff_mult[symmetric] by (simp add: mult.commute)
      also have "... = coeff ?r i"
        unfolding coeff_add coeff_mult Let_def
        unfolding coeff_poly_of_vec dim..
      finally show ?thesis.
  qed
qed

(**** End of the lemmas which could be moved to Algebraic_Numbers/Resultant.thy ****)

(**** The following lemmas could be moved to Computational_Algebra/Polynomial.thy ****)

lemma normalize_field [simp]: "normalize (a :: 'a :: {field, semiring_gcd}) = (if a = 0 then 0 else 1)"
  using unit_factor_normalize by fastforce

lemma content_field [simp]: "content (p :: 'a :: {field,semiring_gcd} poly) = (if p = 0 then 0 else 1)"
  by (induct p, auto simp: content_def)

lemma primitive_part_field [simp]: "primitive_part (p :: 'a :: {field,semiring_gcd} poly) = p"
  by (cases "p = 0", auto intro!: primitive_part_prim)

lemma primitive_part_dvd: "primitive_part a dvd a"
  by (metis content_times_primitive_part dvd_def dvd_refl mult_smult_right)

lemma degree_abs [simp]:
  "degree \<bar>p\<bar> = degree p" by (auto simp: abs_poly_def)

lemma degree_gcd1:
  assumes a_not0: "a \<noteq> 0" 
  shows "degree (gcd a b) \<le> degree a"
proof -
  let ?g = "gcd a b"
  have gcd_dvd_b: "?g dvd a" by simp
  from this obtain c where a_gc: "a = ?g * c" unfolding dvd_def by auto
  have g_not0: "?g \<noteq>0" using a_not0 a_gc by auto
  have c0: "c \<noteq> 0" using a_not0 a_gc by auto
  have "degree ?g \<le> degree (?g * c)" by (rule degree_mult_right_le[OF c0])
  also have "... = degree a" using a_gc by auto
  finally show ?thesis .  
qed

lemma primitive_part_neg [simp]:
  fixes a::"'a :: {factorial_ring_gcd,factorial_semiring_multiplicative} poly"
  shows "primitive_part (-a) = - primitive_part a"
proof -
  have "primitive_part (-a) = primitive_part (smult (-1) a)" by auto
  then show ?thesis unfolding primitive_part_smult
    by (simp add: is_unit_unit_factor)
qed

lemma content_uminus[simp]: 
  fixes f::"int poly"
  shows "content (-f) = content f"
proof -
  have "-f = - (smult 1 f)" by auto
  also have "... = smult (-1) f" using smult_minus_left by auto
  finally have "content (-f) = content (smult (-1) f)" by auto
  also have "... = normalize (- 1) * content f" unfolding content_smult ..
  finally show ?thesis by auto  
qed

lemma pseudo_mod_monic:
  fixes f g :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  defines "r \<equiv> pseudo_mod f g"
  assumes monic_g: "monic g"
  shows "\<exists>q.  f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  let ?cg = "coeff g (degree g)"
  let ?cge = "?cg ^ (Suc (degree f) - degree g)"
  define a where "a = ?cge"
  from r_def[unfolded pseudo_mod_def] obtain q where pdm: "pseudo_divmod f g = (q, r)"
    by (cases "pseudo_divmod f g") auto
  have g: "g \<noteq> 0" using monic_g by auto
  from pseudo_divmod[OF g pdm] have id: "smult a f = g * q + r" and "r = 0 \<or> degree r < degree g"
    by (auto simp: a_def)
  have a1: "a = 1" unfolding a_def using monic_g by auto
  hence id2: "f = g * q + r" using id by auto  
  show "r = 0 \<or> degree r < degree g" by fact  
  from g have "a \<noteq> 0"
    by (auto simp: a_def)  
  with id2 show "\<exists>q. f = g * q + r"
    by auto
qed

lemma monic_imp_div_mod_int_poly_degree: 
  fixes p :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  assumes m: "monic u"
  shows "\<exists>q r. p = q*u + r \<and> (r = 0 \<or> degree r < degree u)" 
  using pseudo_mod_monic[OF m] using mult.commute by metis

corollary monic_imp_div_mod_int_poly_degree2: 
  fixes p :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  assumes m: "monic u" and deg_u: "degree u > 0"
  shows "\<exists>q r. p = q*u + r \<and> (degree r < degree u)"
proof -  
  obtain q r where "p = q * u + r" and r: "(r = 0 \<or> degree r < degree u)" 
      using monic_imp_div_mod_int_poly_degree[OF m, of p] by auto
    moreover have "degree r < degree u" using deg_u r by auto  
  ultimately show ?thesis by auto
qed
(**** End of the lemmas that could be moved to Computational_Algebra/Polynomial.thy ****)


(* To be categorized *)
lemma (in zero_hom) hom_upper_triangular:
  "A \<in> carrier_mat n n \<Longrightarrow> upper_triangular A \<Longrightarrow> upper_triangular (map_mat hom A)"
  by (auto simp: upper_triangular_def)

end
