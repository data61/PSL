(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Newton Interpolation\<close>

text \<open>We proved the soundness of the Newton interpolation, i.e., a method to interpolate a polynomial $p$
  from a list of points $(x_1,p(x_1)), (x_2, p(x_2)), \ldots$. In experiments it performs
  much faster than the Lagrange interpolation.\<close>
theory Newton_Interpolation
imports 
  "HOL-Library.Monad_Syntax"
  Ring_Hom_Poly
  Divmod_Int
  Is_Rat_To_Rat
begin

text \<open>For the Newton interpolation, we start with an efficient implementation (which in prior examples
  we used as an uncertified oracle). Later on, a more abstract definition of the algorithm
  is described for which soundness is proven, and which is provably equivalent to the efficient
  implementation.

  The implementation is based on divided differences and the Horner schema.\<close>

fun horner_composition :: "'a :: comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a poly" where
  "horner_composition [cn] xis = [:cn:]"
| "horner_composition (ci # cs) (xi # xis) = horner_composition cs xis * [:- xi, 1:] + [:ci:]"
| "horner_composition _ _ = 0"

lemma (in map_poly_comm_ring_hom) horner_composition_hom:
  "horner_composition (map hom cs) (map hom xs) = map_poly hom (horner_composition cs xs)"
  by (induct cs xs rule: horner_composition.induct, auto simp: hom_distribs)

lemma horner_coeffs_ints: assumes len: "length cs \<le> Suc (length ys)"
  shows "(set (coeffs (horner_composition cs (map rat_of_int ys))) \<subseteq> \<int>) = (set cs \<subseteq> \<int>)"
proof -
  let ?ir = "int_of_rat"
  let ?ri = "rat_of_int"
  let ?mir = "map ?ir"
  let ?mri = "map ?ri"
  show ?thesis
  proof
    define ics where "ics = map ?ir cs"
    assume "set cs \<subseteq> \<int>"
    hence ics: "cs = ?mri ics" unfolding ics_def map_map o_def
      by (simp add: map_idI subset_code(1))      
    show "set (coeffs (horner_composition cs (?mri ys))) \<subseteq> \<int>"
      unfolding ics of_int_poly_hom.horner_composition_hom by auto
  next
    assume "set (coeffs (horner_composition cs (?mri ys))) \<subseteq> \<int>"
    thus "set cs \<subseteq> \<int>" using len
    proof (induct cs arbitrary: ys)
      case (Cons c cs xs)
      show ?case
      proof (cases "cs = [] \<or> xs = []")
        case True
        with Cons show ?thesis by (cases "c = 0"; cases cs, auto)
      next
        case False
        then obtain d ds and y ys where cs: "cs = d # ds" and xs: "xs = y # ys" 
          by (cases cs, auto, cases xs, auto)
        let ?q = "horner_composition cs (?mri ys)"
        define q where "q = ?q"
        define p where "p = q * [:- ?ri y, 1:] + [:c:]"
        have id: "horner_composition (c # cs) (?mri xs) = p" 
          unfolding cs xs q_def p_def by simp
        have coeff: "coeff p i \<in> \<int>" for i
        proof (cases "coeff p i \<in> set (coeffs p)")
          case True
          with Cons(2)[unfolded id] show ?thesis by blast
        next
          case False
          hence "coeff p i = 0" using range_coeff[of p] by blast
          thus ?thesis by simp
        qed
        {
          fix i
          let ?f = "\<lambda> j. coeff [:- ?ri y, 1:] j * coeff q (Suc i - j)"
          have "coeff p (Suc i) = coeff ([: -?ri y, 1 :] * q) (Suc i)" unfolding p_def by simp
          also have "\<dots> = (\<Sum>j\<le>Suc i. ?f j)" unfolding coeff_mult by simp
          also have "\<dots> = ?f 0 + ?f 1 + (\<Sum>j\<in>{..Suc i} - {0} - {Suc 0}. ?f j)"
            by (subst sum.remove[of _ 0], force+, subst sum.remove[of _ 1], force+)
          also have "(\<Sum>j\<in>{..Suc i} - {0} - {Suc 0}. ?f j) = 0"
          proof (rule sum.neutral, auto, goal_cases)
            case (1 x)
            thus ?case by (cases x, auto, cases "x - 1", auto)
          qed
          also have "?f 0 = - ?ri y * coeff q (Suc i)" by simp
          also have "?f 1 = coeff q i" by simp
          finally have int: "coeff q i - ?ri y * coeff q (Suc i) \<in> \<int>" using coeff[of "Suc i"] by auto
          assume "coeff q (Suc i) \<in> \<int>"
          hence "?ri y * coeff q (Suc i) \<in> \<int>" by simp
          hence "coeff q i \<in> \<int>" using int Ints_diff Ints_minus by force
        } note coeff_q = this
        {
          fix i
          assume "i \<le> degree q"
          hence "coeff q (degree q - i) \<in> \<int>"
          proof (induct i)
            case 0
            from coeff_q[of "degree q"] show ?case
              by (metis Ints_0 Suc_n_not_le_n diff_zero le_degree)
          next
            case (Suc i)
            with coeff_q[of i] show ?case
              by (metis Suc_diff_Suc Suc_leD Suc_n_not_le_n coeff_q le_less)
          qed
        } note coeff_q = this
        {
          fix i
          have "coeff q i \<in> \<int>"
          proof (cases "i \<le> degree q")
            case True
            with coeff_q[of "degree q - i"] show ?thesis by auto
          next
            case False
            hence "coeff q i = 0" using le_degree by blast
            thus ?thesis by simp
          qed
        } note coeff_q = this
        hence "set (coeffs q) \<subseteq> \<int>" by (auto simp: coeffs_def)
        
        from Cons(1)[OF this[unfolded q_def]] Cons(3) xs have IH: "set cs \<subseteq> \<int>" by auto
        define r where "r = coeff q 0 * (- ?ri y)"
        have r: "r \<in> \<int>" using coeff_q[of 0] unfolding r_def by auto
        have "coeff p 0 \<in> \<int>" by fact
        also have "coeff p 0 = r + c" unfolding p_def r_def by simp
        finally have c: "c \<in> \<int>" using r using Ints_diff by force
        with IH show ?thesis by auto
      qed
    qed simp
  qed
qed

context
fixes 
  ty :: "'a :: field itself"
  and xs :: "'a list"
  and fs :: "'a list"
begin


fun divided_differences_impl :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "divided_differences_impl (xi_j1 # x_j1s) fj xj (xi # xis) = (let 
    x_js = divided_differences_impl x_j1s fj xj xis;
    new = (hd x_js - xi_j1) / (xj - xi)
    in new # x_js)"
| "divided_differences_impl [] fj xj xis = [fj]"

fun newton_coefficients_main :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "newton_coefficients_main [fj] xjs = [[fj]]"
| "newton_coefficients_main (fj # fjs) (xj # xjs) = (
    let rec = newton_coefficients_main fjs xjs; row = hd rec;
      new_row = divided_differences_impl row fj xj xs
    in new_row # rec)"
| "newton_coefficients_main _ _ = []"

definition newton_coefficients :: "'a list" where
  "newton_coefficients = map hd (newton_coefficients_main (rev fs) (rev xs))"

definition newton_poly_impl :: "'a poly" where
  "newton_poly_impl = horner_composition (rev newton_coefficients) xs"

qualified definition "x i = xs ! i"
qualified definition "f i = fs ! i"

private definition "xd i j = x i - x j"

lemma [simp]: "xd i i = 0" "xd i j + xd j k = xd i k" "xd i j + xd k i = xd k j" 
  unfolding xd_def by simp_all

(* divided differences [xi,..,xj]f *)
private function xij_f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "xij_f i j = (if i < j then (xij_f (i + 1) j - xij_f i (j - 1)) / xd j i else f i)"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,j). j - i)", auto)

private definition c :: "nat \<Rightarrow> 'a" where
  "c i = xij_f 0 i"

private definition "X j = [: - x j, 1:]"

private function b :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "b i n = (if i \<ge> n then [:c n:] else b (Suc i) n * X i + [:c i:])"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,n). Suc n - i)", auto)

declare b.simps[simp del]

definition newton_poly :: "nat \<Rightarrow> 'a poly" where
  "newton_poly n = b 0 n"

private definition "Xij i j = prod_list (map X [i ..< j])"

private definition "N i = Xij 0 i"

lemma Xii_1[simp]: "Xij i i = 1" unfolding Xij_def by simp
lemma smult_1[simp]: "smult d 1 = [:d:]"
  by (fact smult_one)

private lemma newton_poly_sum: 
  "newton_poly n = sum_list (map (\<lambda> i. smult (c i) (N i)) [0 ..< Suc n])"
  unfolding newton_poly_def N_def
proof -
  {
    fix j
    assume "j \<le> n"
    hence "b j n = (\<Sum>i\<leftarrow>[j..<Suc n]. smult (c i) (Xij j i))"
    proof (induct j n rule: b.induct)
      case (1 j n)
      show ?case
      proof (cases "j \<ge> n")
        case True
        with 1(2) have j: "j = n" by auto
        hence "b j n = [:c n:]" unfolding b.simps[of j n] by simp
        thus ?thesis unfolding j by simp
      next
        case False
        hence b: "b j n = b (Suc j) n * X j + [: c j:]" unfolding b.simps[of j n] by simp
        define nn where "nn = Suc n"
        from 1(2) have id: "[j..< nn] = j # [Suc j ..< nn]" unfolding nn_def by (simp add: upt_rec)
        from False have "Suc j \<le> n" by auto
        note IH = 1(1)[OF False this]
        have id2: "(\<Sum>x\<leftarrow>[Suc j..< nn]. smult (c x) (Xij (Suc j) x * X j)) =
          (\<Sum>i\<leftarrow>[Suc j..< nn]. smult (c i) (Xij j i))"
        proof (rule arg_cong[of _ _ sum_list], rule map_ext, intro impI, goal_cases)
          case (1 i)
          hence "Xij (Suc j) i * X j = Xij j i" by (simp add: Xij_def upt_conv_Cons)
          thus ?case by simp
        qed
        show ?thesis unfolding b IH sum_list_mult_const[symmetric]
          unfolding nn_def[symmetric] id
          by (simp add: id2)
      qed
    qed
  }
  from this[of 0] show "b 0 n = (\<Sum>i\<leftarrow>[0..<Suc n]. smult (c i) (Xij 0 i))" by simp
qed

private lemma poly_newton_poly: "poly (newton_poly n) y = sum_list (map (\<lambda> i. c i * poly (N i) y) [0 ..< Suc n])"
  unfolding newton_poly_sum poly_sum_list map_map o_def by simp

private definition "pprod k i j = (\<Prod>l\<leftarrow>[i..<j]. xd k l)"

private lemma poly_N_xi: "poly (N i) (x j) = pprod j 0 i"
proof -
  have "poly (N i) (x j) = (\<Prod>l\<leftarrow>[0..<i]. xd j l)"
    unfolding N_def Xij_def poly_prod_list X_def[abs_def] map_map o_def xd_def by simp
  also have "\<dots> = pprod j 0 i" unfolding pprod_def ..
  finally show ?thesis .
qed

private lemma poly_N_xi_cond: "poly (N i) (x j) = (if j < i then 0 else pprod j 0 i)"
proof -
  show ?thesis
  proof (cases "j < i")
    case False
    thus ?thesis using poly_N_xi by simp
  next
    case True
    hence "j \<in> set [0 ..< i]" by auto
    from split_list[OF this] obtain bef aft where id2: "[0 ..< i] = bef @ j # aft" by auto
    have "(\<Prod>k\<leftarrow>[0..<i]. xd j k) = 0" unfolding id2 by auto
    with True show ?thesis unfolding poly_N_xi pprod_def by auto
  qed
qed

private lemma poly_newton_poly_xj: assumes "j \<le> n"
  shows "poly (newton_poly n) (x j) = sum_list (map (\<lambda> i. c i * poly (N i) (x j)) [0 ..< Suc j])"
proof -
  from assms have id: "[0 ..< Suc n] = [0 ..< Suc j] @ [Suc j ..< Suc n]" 
    by (metis Suc_le_mono le_Suc_ex less_eq_nat.simps(1) upt_add_eq_append)
  have id2: "(\<Sum>i\<leftarrow>[Suc j..< Suc n]. c i * poly (N i) (x j)) = 0"
    by (rule sum_list_neutral, unfold poly_N_xi_cond, auto)
  show ?thesis unfolding poly_newton_poly id map_append sum_list_append id2 by simp
qed

declare xij_f.simps[simp del]

context
  fixes n
  assumes dist: "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
begin
private lemma xd_diff: "i < j \<Longrightarrow> j \<le> n \<Longrightarrow> xd i j \<noteq> 0"
   "i < j \<Longrightarrow> j \<le> n \<Longrightarrow> xd j i \<noteq> 0" using dist[of i j] dist[of j i] unfolding xd_def by auto

text \<open>This is the key technical lemma for soundness of Newton interpolation.\<close>

private lemma divided_differences_main: assumes "k \<le> n" "i < k"
  shows "sum_list (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i]) = 
  sum_list (map (\<lambda> j. xij_f (Suc i) (Suc i + j) * pprod k (Suc i) (Suc i + j)) [0..<Suc k - Suc i])"
proof -
  let ?exp = "\<lambda> i j. xij_f i (i + j) * pprod k i (i + j)"
  define ei where "ei = ?exp i"
  define esi where "esi = ?exp (Suc i)"  
  let ?ki = "k - i"
  let ?sumi = "\<lambda> xs. sum_list (map ei xs)"
  let ?sumsi = "\<lambda> xs. sum_list (map esi xs)"
  let ?mid = "\<lambda> j. xij_f i (k - j) * pprod k (Suc i) (k - j) * xd (k - j) i"
  let ?sum = "\<lambda> j. ?sumi [0 ..< ?ki - j] + ?sumsi [?ki - j ..< ?ki] + ?mid j"
  define fin where "fin = ?ki - 1"
  have fin: "fin < ?ki" unfolding fin_def using assms by auto
  have id: "[ 0 ..< Suc k - i] = [0 ..< ?ki] @ [?ki]" and 
    id2: "[i..<k] = i # [Suc i ..< k]" and
    id3: "k - (i + (k - Suc i)) = 1" "k - (?ki - 1) = Suc i" using assms 
    by (auto simp: Suc_diff_le upt_conv_Cons)
  have neq: "xd (Suc i) i \<noteq> 0" using xd_diff[of i "Suc i"] assms by auto
  have "sum_list (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i])
    = ?sumi [0 ..< Suc k - i]" unfolding ei_def by simp
  also have "\<dots> = ?sumi [0 ..< ?ki] + ?sumsi [?ki ..< ?ki] + ei ?ki" 
    unfolding id by simp
  also have "\<dots> = ?sum 0"
    unfolding ei_def using assms by (simp add: pprod_def id2)
  also have "?sum 0 = ?sum fin" using fin
  proof (induct fin)
    case (Suc fin)
    from Suc(2) assms 
    have fki: "fin < ?ki" and ikf: "i < k - Suc fin" "i < k - fin" and kfn: "k - fin \<le> n" by auto
    from xd_diff[OF ikf(2) kfn] have nz: "xd (k - fin) i \<noteq> 0" by auto
    note IH = Suc(1)[OF fki]
    have id4: "[0 ..< ?ki - fin] = [0 ..< ?ki - Suc fin] @ [?ki - Suc fin]" 
      "i + (k - i - Suc fin) = k - Suc fin" 
      "Suc (k - Suc fin) = k - fin" using Suc(2) assms  \<open>fin < ?ki\<close>
      by (metis Suc_diff_Suc le0 upt_Suc) (insert Suc(2), auto)      
    from Suc(2) assms have id5: "[i..<k - Suc fin] = i # [Suc i ..< k - Suc fin]"
      "[Suc i..<k - fin] = [Suc i..<k - Suc fin] @ [k - Suc fin]"
      by (force simp: upt_rec) (metis Suc_leI id4(3) ikf(1) upt_Suc)
    have "?sum 0 = ?sum fin" by (rule IH)
    also have "\<dots> = ?sumi [0 ..< ?ki - Suc fin] + ?sumsi [?ki - fin ..< ?ki] + 
      (ei (?ki - Suc fin) + ?mid fin)"
      unfolding id4 by simp
    also have "?mid fin = (xij_f (Suc i) (k - fin) - xij_f i (k - Suc fin))
      * pprod k (Suc i) (k - fin)" unfolding xij_f.simps[of i "k - fin"]
      using ikf nz by simp
    also have "\<dots> = xij_f (Suc i) (k - fin) * pprod k (Suc i) (k - fin) -
      xij_f i (k - Suc fin) * pprod k (Suc i) (k - fin)" by algebra
    also have "xij_f (Suc i) (k - fin) * pprod k (Suc i) (k - fin) = esi (?ki - Suc fin)"
      unfolding esi_def using ikf by (simp add: id4)
    also have "ei (?ki - Suc fin) = xij_f i (k - Suc fin) * pprod k i (k - Suc fin)"       
      unfolding ei_def id4 using ikf by (simp add: ac_simps)
    finally have "?sum 0 = ?sumi [0 ..< ?ki - Suc fin] 
      + (esi (?ki - Suc fin) + ?sumsi [?ki - fin ..< ?ki])
      + (xij_f i (k - Suc fin) * (pprod k i (k - Suc fin) - pprod k (Suc i) (k - fin)))"
      by algebra
    also have "esi (?ki - Suc fin) + ?sumsi [?ki - fin ..< ?ki] 
      = ?sumsi ((?ki - Suc fin) # [?ki - fin ..< ?ki])" by simp
    also have "(?ki - Suc fin) # [?ki - fin ..< ?ki] = [?ki - Suc fin ..< ?ki]"
      using Suc(2) by (simp add: Suc_diff_Suc upt_rec)
    also have "pprod k i (k - Suc fin) - pprod k (Suc i) (k - fin) 
      = (xd k i) * pprod k (Suc i) (k - Suc fin) - (xd k (k - Suc fin)) * pprod k (Suc i) (k - Suc fin)"
      unfolding pprod_def id5 by simp
    also have "\<dots> = (xd k i - xd k (k - Suc fin)) * pprod k (Suc i) (k - Suc fin)"
      by algebra
    also have "\<dots> = (xd (k - Suc fin) i) * pprod k (Suc i) (k - Suc fin)" unfolding xd_def by simp
    also have "xij_f i (k - Suc fin) * \<dots> = ?mid (Suc fin)" by simp
    finally show ?case by simp
  qed simp
  also have "\<dots> = (ei 0 + ?mid (k - i - 1)) + ?sumsi [1 ..< k - i]" 
    unfolding fin_def by (simp add: id3)
  also have "ei 0 + ?mid (k - i - 1) = esi 0" unfolding id3
    unfolding ei_def esi_def xij_f.simps[of i i]  using neq assms
    by (simp add: field_simps xij_f.simps pprod_def)
  also have "esi 0 + ?sumsi [1 ..< k - i] = ?sumsi (0 # [1 ..< k - i])" by simp
  also have "0 # [1 ..< k - i] = [0 ..< Suc k - Suc i]" 
    using assms by (simp add: upt_rec)
  also have "?sumsi \<dots> = sum_list (map (\<lambda> j. xij_f (Suc i) (Suc i + j) * 
    pprod k (Suc i) (Suc i + j)) [0..<Suc k - Suc i])"
    unfolding esi_def using assms by simp
  finally show ?thesis .
qed

private lemma divided_differences: assumes kn: "k \<le> n" and ik: "i \<le> k"
  shows "sum_list (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i]) = f k"
proof -
  {
    fix ii
    assume "i + ii \<le> k"
    hence "sum_list (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i])
      = sum_list (map (\<lambda> j. xij_f (i + ii) (i + ii + j) * pprod k (i + ii) (i + ii + j)) [0..<Suc k - (i + ii)])"
    proof (induct ii)
      case (Suc ii)
      hence le1: "i + ii \<le> k" and le2: "i + ii < k" by simp_all
      show ?case unfolding Suc(1)[OF le1] unfolding divided_differences_main[OF kn le2]
        using Suc(2) by simp
    qed simp
  } note main = this
  have ik: "i + (k - i) \<le> k" and id: "i + (k - i) = k" using ik by simp_all
  show ?thesis unfolding main[OF ik] unfolding id
    by (simp add: xij_f.simps pprod_def)
qed      

lemma newton_poly_sound: assumes "k \<le> n"
  shows "poly (newton_poly n) (x k) = f k"
proof -
  have "poly (newton_poly n) (x k) = 
    sum_list (map (\<lambda> j. xij_f 0 (0 + j) * pprod k 0 (0 + j)) [0..<Suc k - 0])"
    unfolding poly_newton_poly_xj[OF assms] c_def poly_N_xi by simp
  also have "\<dots> = f k"
    by (rule divided_differences[OF assms], simp)
  finally show ?thesis by simp
qed
end

lemma newton_poly_degree: "degree (newton_poly n) \<le> n" 
proof -
  {
    fix i
    have "i \<le> n \<Longrightarrow> degree (b i n) \<le> n - i"
    proof (induct i n rule: b.induct)
      case (1 i n)
      note b = b.simps[of i n]
      show ?case 
      proof (cases "n \<le> i")
        case True
        thus ?thesis unfolding b by auto
      next
        case False
        have "degree (b i n) = degree (b (Suc i) n * X i + [:c i:])" using False unfolding b by simp
        also have "\<dots> \<le> max (degree (b (Suc i) n * X i)) (degree [:c i:])"
          by (rule degree_add_le_max)
        also have "\<dots> = degree (b (Suc i) n * X i)" by simp
        also have "\<dots> \<le> degree (b (Suc i) n) + degree (X i)"
          by (rule degree_mult_le)
        also have "\<dots> \<le> n - Suc i + degree (X i)" 
          using 1(1)[OF False] 1(2) False add_le_mono1 not_less_eq_eq by blast
        also have "\<dots> = n - Suc i + 1" unfolding X_def by simp
        also have "\<dots> = n - i" using 1(2) False by auto
        finally show ?thesis .
      qed
    qed
  }
  from this[of 0] show ?thesis unfolding newton_poly_def by simp
qed

context
  fixes n
  assumes xs: "length xs = n"
    and fs: "length fs = n"
begin
lemma newton_coefficients_main: 
  "k < n \<Longrightarrow> newton_coefficients_main (rev (map f [0..<Suc k])) (rev (map x [0..<Suc k]))
    = rev (map (\<lambda> i. map (\<lambda> j. xij_f j i) [0..<Suc i]) [0..<Suc k])"
proof (induct k)
  case 0
  show ?case
    by (simp add: xij_f.simps)
next
  case (Suc k)
  hence "k < n" by auto
  note IH = Suc(1)[OF this]
  have id: "\<And> f. rev (map f [0..<Suc (Suc k)]) = f (Suc k) # f k # rev (map f [0..< k])" 
    and id2: "\<And> f. f k # rev (map f [0..<k]) = rev (map f [0..< Suc k])" by simp_all
  show ?case unfolding id newton_coefficients_main.simps Let_def
    unfolding id2 IH
    unfolding list.simps id2[symmetric]
  proof (rule conjI, goal_cases)
    case 1
    have xs: "xs = map x [0 ..< n]" using xs unfolding x_def[abs_def] 
      by (intro nth_equalityI, auto)
    define nn where "nn = (0 :: nat)"
    define m where "m = Suc k - nn"
    have prems: "m = Suc k - nn" "nn < Suc (Suc k)" unfolding m_def nn_def by auto
    have "?case = (divided_differences_impl (map ((\<lambda>j. xij_f j k)) [nn..< Suc k]) (f (Suc k)) (x (Suc k)) (map x [nn ..< n]) =
      map ((\<lambda>j. xij_f j (Suc k))) [nn..<Suc (Suc k)])"
      unfolding nn_def xs[symmetric] by simp
    also have "\<dots>" using prems
    proof (induct m arbitrary: nn)
      case 0
      hence nn: "nn = Suc k" by auto
      show ?case unfolding nn by (simp add: xij_f.simps)
    next
      case (Suc m)
      with \<open>Suc k < n\<close> have "nn < n" and le: "nn < Suc k" by auto
      with Suc(2-) have id: 
        "[nn..<Suc k] = nn # [Suc nn..< Suc k]"
        "[nn..<n] = nn # [Suc nn..< n]"
      and id2: "[nn..<Suc (Suc k)] = nn # [Suc nn..<Suc (Suc k)]"
        "[Suc nn..<Suc (Suc k)] = Suc nn # [Suc (Suc nn)..<Suc (Suc k)]"
        by (auto simp: upt_rec)
      from Suc(2-) have "m = Suc k - Suc nn" "Suc nn < Suc (Suc k)" by auto
      note IH = Suc(1)[OF this]
      show ?case unfolding id list.simps divided_differences_impl.simps IH Let_def
        unfolding id2 list.simps 
        using le
        by (simp add: xij_f.simps[of nn "Suc k"] xd_def)
    qed
    finally show ?case by simp
  qed simp
qed

lemma newton_coefficients: "newton_coefficients = rev (map c [0 ..< n])"
proof (cases n)
  case 0
  hence xs: "xs = []" "fs = []" using xs fs by auto
  show ?thesis unfolding newton_coefficients_def 0 
    using newton_coefficients_main.simps
    unfolding xs by simp
next
  case (Suc nn)
  hence sn: "Suc nn = n" and nn: "nn < n" by auto
  from fs have fs: "map f [0..<Suc nn] = fs" unfolding sn
    by (intro nth_equalityI, auto simp: f_def)
  from xs have xs: "map x [0..<Suc nn] = xs" unfolding sn
    by (intro nth_equalityI, auto simp: x_def)
  show ?thesis
    unfolding newton_coefficients_def
      newton_coefficients_main[OF nn, unfolded fs xs]
    unfolding sn rev_map[symmetric] map_map o_def 
    by (rule arg_cong[of _ _ rev], subst upt_rec, intro nth_equalityI, auto simp: c_def)
qed

lemma newton_poly_impl: assumes "n = Suc nn"
  shows "newton_poly_impl = newton_poly nn"
proof -
  define i where "i = (0 :: nat)"
  have xs: "map x [0..<n] = xs" using xs
    by (intro nth_equalityI, auto simp: x_def)
  have "i \<le> nn" unfolding i_def by simp
  hence "horner_composition (map c [i..<Suc nn]) (map x [i..<Suc nn]) = b i nn"
  proof (induct i nn rule: b.induct)
    case (1 i n)
    show ?case
    proof (cases "n \<le> i")
      case True
      with 1(2) have i: "i = n" by simp
      show ?thesis unfolding i b.simps[of n n] by simp
    next
      case False
      hence "Suc i \<le> n" by simp
      note IH = 1(1)[OF False this]
      have bi: "b i n = b (Suc i) n * X i + [:c i:]" using False by (simp add: b.simps)    
      from False have id: "[i ..< Suc n] = i # [Suc i ..< Suc n]" by (simp add: upt_rec)
      from False have id2: "[Suc i ..< Suc n] = Suc i # [Suc (Suc i) ..< Suc n]" by (simp add: upt_rec)
      show ?thesis unfolding id bi list.simps horner_composition.simps id2
        unfolding IH[unfolded id2 list.simps] by (simp add: X_def)
    qed
  qed
  thus ?thesis
    unfolding newton_poly_impl_def newton_coefficients rev_rev_ident newton_poly_def i_def
      assms[symmetric] xs .
qed
end
end

context 
  fixes xs fs :: "int list"
begin

fun divided_differences_impl_int :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list option" where
  "divided_differences_impl_int (xi_j1 # x_j1s) fj xj (xi # xis) = (
     case divided_differences_impl_int x_j1s fj xj xis of None \<Rightarrow> None
   | Some x_js \<Rightarrow> let (new,m) = divmod_int (hd x_js - xi_j1) (xj - xi)
     in if m = 0 then Some (new # x_js) else None)"
| "divided_differences_impl_int [] fj xj xis = Some [fj]"
   
fun newton_coefficients_main_int :: "int list \<Rightarrow> int list \<Rightarrow> int list list option" where
  "newton_coefficients_main_int [fj] xjs = Some [[fj]]"
| "newton_coefficients_main_int (fj # fjs) (xj # xjs) = (do {
    rec \<leftarrow> newton_coefficients_main_int fjs xjs;
    let row = hd rec;
    new_row \<leftarrow> divided_differences_impl_int row fj xj xs;
    Some (new_row # rec)})"
| "newton_coefficients_main_int _ _ = Some []"

definition newton_coefficients_int :: "int list option" where
  "newton_coefficients_int = map_option (map hd) (newton_coefficients_main_int (rev fs) (rev xs))"

lemma divided_differences_impl_int_Some:
  "length gs \<le> length ys 
  \<Longrightarrow> divided_differences_impl_int gs g x ys = Some res
  \<Longrightarrow> divided_differences_impl (map rat_of_int gs) (rat_of_int g) (rat_of_int x) (map rat_of_int ys) = map rat_of_int res
    \<and> length res = Suc (length gs)"
proof (induct gs g x ys arbitrary: res rule: divided_differences_impl_int.induct)
  case (1 xi_j1 x_j1s fj xj xi xis)
  note some = 1(3)
  from 1(2) have len: "length x_j1s \<le> length xis" by auto
  from some obtain x_js where rec: "divided_differences_impl_int x_j1s fj xj xis = Some x_js"
    by (auto split: option.splits)
  note IH = 1(1)[OF len rec]
  have id: "hd (map rat_of_int x_js) = rat_of_int (hd x_js)" using IH by (cases x_js, auto)
  from some[simplified, unfolded rec divmod_int_def] have mod: "(hd x_js - xi_j1) mod (xj - xi) = 0"
    and res: "res = (hd x_js - xi_j1) div (xj - xi) # x_js" by (auto split: if_splits)
  have "rat_of_int ((hd x_js - xi_j1) div (xj - xi)) = rat_of_int (hd x_js - xi_j1) / rat_of_int (xj - xi)"
    using mod by force
  hence "(rat_of_int (hd x_js) - rat_of_int xi_j1) / (rat_of_int xj - rat_of_int xi) = 
    rat_of_int ((hd x_js - xi_j1) div (xj - xi))"
    by simp
  thus ?case by (simp add: IH Let_def res id)
next
  case (2 fj xj xis res)
  hence res: "res = [fj]" by simp
  thus ?case by simp
qed simp

lemma div_Ints_mod_0: assumes "rat_of_int a / rat_of_int b \<in> \<int>" "b \<noteq> 0"
  shows "a mod b = 0"
proof -
  define c where "c = int_of_rat (rat_of_int a / rat_of_int b)"
  have "rat_of_int a / rat_of_int b = rat_of_int c" unfolding c_def using assms(1) by simp
  hence "rat_of_int a = rat_of_int b * rat_of_int c" using assms(2)
    by (metis divide_cancel_right nonzero_mult_div_cancel_left of_int_eq_0_iff)
  hence a: "a = b * c" by (simp add: of_int_hom.injectivity)
  show "a mod b = 0" unfolding a by simp
qed

lemma divided_differences_impl_int_None:
  "length gs \<le> length ys 
  \<Longrightarrow> divided_differences_impl_int gs g x ys = None
  \<Longrightarrow> x \<notin> set (take (length gs) ys)
  \<Longrightarrow> hd (divided_differences_impl (map rat_of_int gs) (rat_of_int g) (rat_of_int x) (map rat_of_int ys)) \<notin> \<int>"
proof (induct gs g x ys rule: divided_differences_impl_int.induct)
  case (1 xi_j1 x_j1s fj xj xi xis)
  note none = 1(3)
  from 1(2,4) have len: "length x_j1s \<le> length xis" and xj: "xj \<notin> set (take (length x_j1s) xis)" and xji: "xj \<noteq> xi" by auto
  define d where "d = divided_differences_impl (map rat_of_int x_j1s) (rat_of_int fj) (rat_of_int xj) (map rat_of_int xis)"
  note IH = 1(1)[OF len _ xj]
  show ?case
  proof (cases "divided_differences_impl_int x_j1s fj xj xis")
    case None
    from IH[OF None] have d: "hd d \<notin> \<int>" unfolding d_def by auto
    {
      let ?x = "(hd d - rat_of_int xi_j1) / (rat_of_int xj - rat_of_int xi)"
      assume "?x \<in> \<int>"
      hence "?x * (of_int (xj - xi)) + rat_of_int xi_j1 \<in> \<int>"
        using Ints_mult Ints_add Ints_of_int by blast
      also have "?x * (of_int (xj - xi)) = hd d - rat_of_int xi_j1" using xji by auto
      also have "\<dots> + rat_of_int xi_j1 = hd d" by simp
      finally have False using d by simp
    }
    thus ?thesis 
      by (auto simp: Let_def d_def[symmetric])
  next
    case (Some res)
    from divided_differences_impl_int_Some[OF len Some]
    have id: "divided_differences_impl (map rat_of_int x_j1s) (rat_of_int fj) (rat_of_int xj) (map rat_of_int xis) =
      map rat_of_int res" and res: "res \<noteq> []" by auto
    have hd: "hd (map rat_of_int res) = of_int (hd res)" using res by (cases res, auto)
    define a where "a = (hd res - xi_j1)"
    define b where "b = xj - xi"
    from none[simplified, unfolded Some divmod_int_def] 
    have mod: "a mod b \<noteq> 0"
      by (auto split: if_splits simp: a_def b_def)
    {
      assume "(rat_of_int (hd res) - rat_of_int xi_j1) / (rat_of_int xj - rat_of_int xi) \<in> \<int>"
      hence "rat_of_int a / rat_of_int b \<in> \<int>" unfolding a_def b_def by simp
      moreover have "b \<noteq> 0" using xji unfolding b_def by simp
      ultimately have False using mod div_Ints_mod_0 by auto
    }
    thus ?thesis 
      by (auto simp: id Let_def hd)
  qed
qed auto
  
lemma newton_coefficients_main_int_Some:
  "length gs = length ys \<Longrightarrow> length ys \<le> length xs  
  \<Longrightarrow> newton_coefficients_main_int gs ys = Some res
  \<Longrightarrow> newton_coefficients_main (map rat_of_int xs) (map rat_of_int gs) (map rat_of_int ys) = map (map rat_of_int) res
    \<and> (\<forall> x \<in> set res. x \<noteq> [] \<and> length x \<le> length ys) \<and> length res = length gs"
proof (induct gs ys arbitrary: res rule: newton_coefficients_main_int.induct)
  case (2 fv v va xj xjs res)
  from 2(2,3) have len: "length (v # va) = length xjs" "length xjs \<le> length xs" by auto
  note some = 2(4)
  let ?n = "newton_coefficients_main_int (v # va) xjs"
  let ?ri = rat_of_int
  let ?mri = "map ?ri"
  from some obtain rec where n: "?n = Some rec"
    by (cases ?n, auto)
  note some = some[simplified, unfolded n]
  let ?d = "divided_differences_impl_int (hd rec) fv xj xs"
  from some obtain dd where d: "?d = Some dd" and res: "res = dd # rec" 
    by (cases ?d, auto)
  note IH = 2(1)[OF len n]
  from IH have lenn: "length (hd rec) \<le> length xjs" by (cases rec, auto)
  with len have "length (hd rec) \<le> length xs" by auto
  note dd = divided_differences_impl_int_Some[OF this d]
  have hd: "hd (map ?mri rec) = ?mri (hd rec)" using IH by (cases rec, auto)
  show ?case unfolding newton_coefficients_main.simps list.simps
    IH[THEN conjunct1, unfolded list.simps] Let_def hd
    dd[THEN conjunct1] res 
  proof (intro conjI)
    show "length (dd # rec) = length (fv # v # va)" using len
      IH[THEN conjunct2] dd[THEN conjunct2] by auto
    show "\<forall>x\<in>insert dd (set rec). x \<noteq> [] \<and> length x \<le> length (xj # xjs)"
      using len IH[THEN conjunct2] dd[THEN conjunct2] lenn by auto
  qed auto
qed auto

lemma newton_coefficients_main_int_None: assumes dist: "distinct xs"
  shows "length gs = length ys \<Longrightarrow> length ys \<le> length xs  
  \<Longrightarrow> newton_coefficients_main_int gs ys = None
  \<Longrightarrow> ys = drop (length xs - length ys) (rev xs)
  \<Longrightarrow> \<exists> row \<in> set (newton_coefficients_main (map rat_of_int xs) (map rat_of_int gs) (map rat_of_int ys)). hd row \<notin> \<int>"
proof (induct gs ys rule: newton_coefficients_main_int.induct)
  case (2 fv v va xj xjs)
  from 2(2,3) have len: "length (v # va) = length xjs" "length xjs \<le> length xs" by auto
  from arg_cong[OF 2(5), of tl] 2(3)
  have xjs: "xjs = drop (length xs - length xjs) (rev xs)"
    by (metis 2(5) butlast_snoc butlast_take length_drop rev.simps(2) rev_drop rev_rev_ident rev_take)
  note none = 2(4)
  let ?n = "newton_coefficients_main_int (v # va) xjs"
  let ?n' = "newton_coefficients_main (map rat_of_int xs) (map rat_of_int (v # va)) (map rat_of_int xjs)"
  let ?ri = rat_of_int
  let ?mri = "map ?ri"
  show ?case
  proof (cases ?n)
    case None
    from 2(1)[OF len None xjs] obtain row where 
      row: "row\<in>set ?n'" and "hd row \<notin> \<int>" by auto
    thus ?thesis by (intro bexI[of _ row], auto simp: Let_def)
  next
    case (Some rec)
    note some = newton_coefficients_main_int_Some[OF len this]
    hence len': "length (hd rec) \<le> length xjs" by (cases rec, auto)
    hence lenn: "length (hd rec) \<le> length xs" using len by auto
    have hd: "hd (map ?mri rec) = ?mri (hd rec)" using some by (cases rec, auto)
    let ?d = "divided_differences_impl_int (hd rec) fv xj xs"
    from none[simplified, unfolded Some]
    have none: "?d = None" by (cases ?d, auto)
    have "xj \<notin> set (take (length (hd rec)) xs)"
    proof
      assume "xj \<in> set (take (length (hd rec)) xs)"
      then obtain i where "i < length (hd rec)" and xj: "xj = xs ! i" 
        unfolding in_set_conv_nth by auto
      with len' have i: "i < length xjs" by simp
      have "Suc (length xjs) \<le> length xs" using 2(3) by auto
      with i have i0: "i \<noteq> 0"
        by (metis 2(5) Suc_diff_Suc Suc_le_lessD diff_less dist distinct_conv_nth 
          hd_drop_conv_nth length_Cons length_drop length_greater_0_conv length_rev less_le_trans 
          list.sel(1) list.simps(3) nat_neq_iff rev_nth xj xjs)      
      have "xj \<in> set xjs" 
        by (subst xjs, unfold xj in_set_conv_nth, rule exI[of _ "length xjs - Suc i"], insert i 2(3) i0,
           auto simp: rev_nth)
      hence ndist: "\<not> distinct (xj # xjs)" by auto
      from dist have "distinct (rev xs)" by simp
      from distinct_drop[OF this] have "distinct (xj # xjs)" using 2(5) by metis
      with ndist
      show False ..
    qed
    note dd = divided_differences_impl_int_None[OF lenn none this]
    show ?thesis
      by (rule bexI, rule dd, insert some hd, auto)
  qed
qed auto


lemma newton_coefficients_int: assumes dist: "distinct xs"
  and len: "length xs = length fs"
  shows "newton_coefficients_int = (let cs = newton_coefficients (map rat_of_int xs) (map of_int fs)
    in if set cs \<subseteq> \<int> then Some (map int_of_rat cs) else None)" 
proof -
  from len have len: "length (rev fs) = length (rev xs)" "length (rev xs) \<le> length xs" by auto
  show ?thesis
  proof (cases "newton_coefficients_main_int (rev fs) (rev xs)")
    case (Some res)
    have rev: "\<And> xs. map rat_of_int (rev xs) = rev (map of_int xs)" unfolding rev_map ..
    note n = newton_coefficients_main_int_Some[OF len Some, unfolded rev]
    {
      fix row
      assume "row \<in> set res"
      with n have "row \<noteq> []" by auto
      hence id: "hd (map rat_of_int row) = rat_of_int (hd row)" by (cases row, auto)
      also have "\<dots> \<in> \<int>" by auto
      finally have int: "hd (map rat_of_int row) \<in> \<int>" by auto
      have "hd row = int_of_rat (hd (map rat_of_int row))" unfolding id by simp
      note this int
    } 
    thus ?thesis unfolding newton_coefficients_int_def Some newton_coefficients_def n[THEN conjunct1] Let_def option.simps
      by (auto simp: o_def)
  next
    case None
    have "rev xs = drop (length xs - length (rev xs)) (rev xs)" by simp
    from newton_coefficients_main_int_None[OF dist len None this]
    show ?thesis unfolding newton_coefficients_int_def newton_coefficients_def None by (auto simp: Let_def rev_map)
  qed
qed

definition newton_poly_impl_int :: "int poly option" where
  "newton_poly_impl_int \<equiv> case newton_coefficients_int of None \<Rightarrow> None 
     | Some nc \<Rightarrow> Some (horner_composition (rev nc) xs)"

lemma newton_poly_impl_int: assumes len: "length xs = length fs" 
  and dist: "distinct xs"
  shows "newton_poly_impl_int = (let p = newton_poly_impl (map rat_of_int xs) (map of_int fs)
    in if set (coeffs p) \<subseteq> \<int> then Some (map_poly int_of_rat p) else None)"
proof -
  let ?ir = "int_of_rat"
  let ?ri = "rat_of_int"
  let ?mir = "map ?ir"
  let ?mri = "map ?ri"
  let ?nc = "newton_coefficients (?mri xs) (?mri fs)"
  have id: "newton_poly_impl_int = (if set ?nc \<subseteq> \<int>
    then Some (horner_composition (rev (?mir ?nc)) xs) else None)" 
    unfolding newton_poly_impl_int_def newton_coefficients_int[OF dist len] Let_def by simp
  have len: "length (rev ?nc) \<le> Suc (length xs)" 
    unfolding length_rev
    by (subst newton_coefficients[OF refl], insert len, auto) 
  show ?thesis unfolding id
    unfolding newton_poly_impl_def
    unfolding Let_def set_rev rev_map horner_coeffs_ints[OF len]
  proof (rule if_cong[OF refl _ refl], rule arg_cong[of _ _ Some])
    define cs where "cs = rev ?nc"
    define ics where "ics = map ?ir cs"
    assume "set ?nc \<subseteq> \<int>"
    hence "set cs \<subseteq> \<int>" unfolding cs_def by auto
    hence ics: "cs = ?mri ics" unfolding ics_def map_map o_def
      by (simp add: map_idI subset_code(1))      
    have id: "horner_composition (rev ?nc) (?mri xs) = map_poly ?ri (horner_composition ics xs)"
      unfolding cs_def[symmetric] ics
      by (rule of_int_poly_hom.horner_composition_hom)
    show "horner_composition (?mir (rev ?nc)) xs
      = map_poly ?ir (horner_composition (rev ?nc) (?mri xs))"
      unfolding id unfolding cs_def[symmetric] ics_def[symmetric]
      by (subst map_poly_map_poly, auto simp: o_def map_poly_idI)
  qed
qed
end

definition newton_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "newton_interpolation_poly x_fs = (let 
    xs = map fst x_fs; fs = map snd x_fs in
    newton_poly_impl xs fs)"

definition newton_interpolation_poly_int :: "(int \<times> int)list \<Rightarrow> int poly option" where
  "newton_interpolation_poly_int x_fs = (let 
    xs = map fst x_fs; fs = map snd x_fs in
    newton_poly_impl_int xs fs)"   

lemma newton_interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = newton_interpolation_poly xs_ys"
  and xy: "(x,y) \<in> set xs_ys"
  shows "poly p x = y"
proof (cases "length xs_ys")
  case 0
  thus ?thesis using xy by (cases xs_ys, auto)
next
  case (Suc nn)
  let ?xs = "map fst xs_ys" let ?fs = "map snd xs_ys" let ?n = "Suc nn"
  from xy[unfolded set_conv_nth] obtain i where xy: "i \<le> nn" "x = ?xs ! i" "y = ?fs ! i"
    using Suc
    by (metis (no_types, lifting) fst_conv in_set_conv_nth less_Suc_eq_le nth_map snd_conv xy)
  have id: "newton_interpolation_poly xs_ys = newton_poly ?xs ?fs nn"
    unfolding newton_interpolation_poly_def Let_def
    by (rule newton_poly_impl[OF _ _ Suc], auto)
  show ?thesis
    unfolding p id
  proof (rule newton_poly_sound[of nn ?xs _ ?fs, unfolded 
      Newton_Interpolation.x_def Newton_Interpolation.f_def, OF _ xy(1), folded xy(2-)])
    fix i j
    show "i < j \<Longrightarrow> j \<le> nn \<Longrightarrow> ?xs ! i \<noteq> ?xs ! j" using dist Suc nth_eq_iff_index_eq by fastforce
  qed
qed

lemma degree_newton_interpolation_poly:  
  shows "degree (newton_interpolation_poly xs_ys) \<le> length xs_ys - 1"
proof (cases "length xs_ys")
  case 0
  hence id: "xs_ys = []" by (cases xs_ys, auto)
  show ?thesis unfolding 
    id newton_interpolation_poly_def Let_def list.simps newton_poly_impl_def
    Newton_Interpolation.newton_coefficients_def
    by simp
next
  case (Suc nn)
  let ?xs = "map fst xs_ys" let ?fs = "map snd xs_ys" let ?n = "Suc nn"
  have id: "newton_interpolation_poly xs_ys = newton_poly ?xs ?fs nn"
    unfolding newton_interpolation_poly_def Let_def
    by (rule newton_poly_impl[OF _ _ Suc], auto)
  show ?thesis unfolding id using newton_poly_degree[of ?xs ?fs nn] Suc by simp
qed

text \<open>For @{const newton_interpolation_poly_int} at this point we just prove that it 
  is equivalent to perfom an interpolation on the rational numbers, and then check
  whether all resulting coefficients are integers. That this corresponds to a 
  sound and complete interpolation algorithm on the integers is proven in the theory
  Polynomial-Interpolation, cf.\ lemmas newton-interpolation-poly-int-Some/None.\<close>

lemma newton_interpolation_poly_int: assumes dist: "distinct (map fst xs_ys)"
  shows "newton_interpolation_poly_int xs_ys = (let 
     rxs_ys = map (\<lambda> (x,y). (rat_of_int x, rat_of_int y)) xs_ys;
     rp = newton_interpolation_poly rxs_ys
     in if (\<forall> x \<in> set (coeffs rp). is_int_rat x) then
       Some (map_poly int_of_rat rp) else None)"
proof -
  have id1: "map fst (map (\<lambda>(x, y). (rat_of_int x, rat_of_int y)) xs_ys) = map rat_of_int (map fst xs_ys)"
    by (induct xs_ys, auto)
  have id2: "map snd (map (\<lambda>(x, y). (rat_of_int x, rat_of_int y)) xs_ys) = map rat_of_int (map snd xs_ys)"
    by (induct xs_ys, auto)
  have id3: "length (map fst xs_ys) = length (map snd xs_ys)" by auto
  show ?thesis
    unfolding newton_interpolation_poly_def  newton_interpolation_poly_int_def Let_def newton_poly_impl_int[OF id3 dist]
    unfolding id1 id2
    by (rule sym, rule if_cong, auto simp: is_int_rat[abs_def])
qed


hide_const 
  Newton_Interpolation.x
  Newton_Interpolation.f
end
