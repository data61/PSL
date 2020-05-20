(*  
    Author:      Sebastiaan Joosten 
                 René Thiemann
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Complex Algebraic Numbers\<close>

text \<open>Since currently there is no immediate analog of Sturm's theorem for the complex numbers,
  we implement complex algebraic numbers via their real and imaginary part.
  
  The major algorithm in this theory is a factorization algorithm which factors a rational
  polynomial over the complex numbers. 

  This algorithm is then combined with explicit root algorithms to try to factor arbitrary  
  complex polymials.\<close>

theory Complex_Algebraic_Numbers
imports 
  Real_Roots
  Complex_Roots_Real_Poly
  Compare_Complex
  Jordan_Normal_Form.Char_Poly  
  Berlekamp_Zassenhaus.Code_Abort_Gcd
  Interval_Arithmetic
begin

subsection \<open>Complex Roots\<close>
  
abbreviation complex_of_int_poly :: "int poly \<Rightarrow> complex poly" where
  "complex_of_int_poly \<equiv> map_poly of_int"

abbreviation complex_of_rat_poly :: "rat poly \<Rightarrow> complex poly" where
  "complex_of_rat_poly \<equiv> map_poly of_rat"

lemma poly_complex_to_real: "(poly (complex_of_int_poly p) (complex_of_real x) = 0)
  = (poly (real_of_int_poly p) x = 0)"
proof -
  have id: "of_int = complex_of_real o real_of_int" by auto
  interpret cr: semiring_hom complex_of_real by (unfold_locales, auto)
  show ?thesis unfolding id
    by (subst map_poly_map_poly[symmetric], force+)
qed

lemma represents_cnj: assumes "p represents x" shows "p represents (cnj x)"
proof -
  from assms have p: "p \<noteq> 0" and "ipoly p x = 0" by auto
  hence rt: "poly (complex_of_int_poly p) x = 0" by auto
  have "poly (complex_of_int_poly p) (cnj x) = 0"
    by (rule complex_conjugate_root[OF _ rt], subst coeffs_map_poly, auto)
  with p show ?thesis by auto
qed

definition poly_2i :: "int poly" where
  "poly_2i \<equiv> [: 4, 0, 1:]"
  
lemma represents_2i: "poly_2i represents (2 * \<i>)"
  unfolding represents_def poly_2i_def by simp

definition root_poly_Re :: "int poly \<Rightarrow> int poly" where
  "root_poly_Re p = cf_pos_poly (poly_mult_rat (inverse 2) (poly_add p p))"
  
lemma root_poly_Re_code[code]: 
  "root_poly_Re p = (let fs = coeffs (poly_add p p); k = length fs 
     in cf_pos_poly (poly_of_list (map (\<lambda>(fi, i). fi * 2 ^ i) (zip fs [0..<k]))))"
proof -
  have [simp]: "quotient_of (1 / 2) = (1,2)" by eval
  show ?thesis unfolding root_poly_Re_def poly_mult_rat_def poly_mult_rat_main_def Let_def by simp
qed
  
definition root_poly_Im :: "int poly \<Rightarrow> int poly list" where
  "root_poly_Im p = (let fs = factors_of_int_poly 
    (poly_add p (poly_uminus p))
    in remdups ((if (\<exists> f \<in> set fs. coeff f 0 = 0) then [[:0,1:]] else [])) @ 
      [ cf_pos_poly (poly_div f poly_2i) . f \<leftarrow> fs, coeff f 0 \<noteq> 0])"
                          
lemma represents_root_poly:
  assumes "ipoly p x = 0" and p: "p \<noteq> 0"
  shows "(root_poly_Re p) represents (Re x)"
    and "\<exists> q \<in> set (root_poly_Im p). q represents (Im x)"
proof -
  let ?Rep = "root_poly_Re p"
  let ?Imp = "root_poly_Im p"
  from assms have ap: "p represents x" by auto
  from represents_cnj[OF this] have apc: "p represents (cnj x)" .
  from represents_mult_rat[OF _ represents_add[OF ap apc], of "inverse 2"]
  have "?Rep represents (1 / 2 * (x + cnj x))" unfolding root_poly_Re_def Let_def
    by (auto simp: hom_distribs)
  also have "1 / 2 * (x + cnj x) = of_real (Re x)"
    by (simp add: complex_add_cnj)
  finally have Rep: "?Rep \<noteq> 0" and rt: "ipoly ?Rep (complex_of_real (Re x)) = 0" unfolding represents_def by auto
  from rt[unfolded poly_complex_to_real]
  have "ipoly ?Rep (Re x) = 0" .
  with Rep show "?Rep represents (Re x)" by auto 
  let ?q = "poly_add p (poly_uminus p)"
  from represents_add[OF ap, of "poly_uminus p" "- cnj x"] represents_uminus[OF apc] 
  have apq: "?q represents (x - cnj x)" by auto
  from factors_int_poly_represents[OF this] obtain pi where pi: "pi \<in> set (factors_of_int_poly ?q)"
    and appi: "pi represents (x - cnj x)" and irr_pi: "irreducible pi" by auto
  have id: "inverse (2 * \<i>) * (x - cnj x) = of_real (Im x)"
    apply (cases x) by (simp add: complex_split imaginary_unit.ctr legacy_Complex_simps)
  from represents_2i have 12: "poly_2i represents (2 * \<i>)" by simp
  have "\<exists> qi \<in> set ?Imp. qi represents (inverse (2 * \<i>) * (x - cnj x))" 
  proof (cases "x - cnj x = 0")
    case False 
    have "poly poly_2i 0 \<noteq> 0" unfolding poly_2i_def by auto
    from represents_div[OF appi 12 this]
      represents_irr_non_0[OF irr_pi appi False, unfolded poly_0_coeff_0] pi
    show ?thesis unfolding root_poly_Im_def Let_def by (auto intro: bexI[of _ "cf_pos_poly (poly_div pi poly_2i)"])
  next
    case True
    hence id2: "Im x = 0" by (simp add: complex_eq_iff)
    from appi[unfolded True represents_def] have "coeff pi 0 = 0" by (cases pi, auto)
    with pi have mem: "[:0,1:] \<in> set ?Imp" unfolding root_poly_Im_def Let_def by auto
    have "[:0,1:] represents (complex_of_real (Im x))" unfolding id2 represents_def by simp
    with mem show ?thesis unfolding id by auto
  qed
  then obtain qi where qi: "qi \<in> set ?Imp" "qi \<noteq> 0" and rt: "ipoly qi (complex_of_real (Im x)) = 0"
    unfolding id represents_def by auto
  from qi rt[unfolded poly_complex_to_real]
  show "\<exists> qi \<in> set ?Imp. qi represents (Im x)" by auto 
qed
  
text \<open>Determine complex roots of a polynomial, 
   intended for polynomials of degree 3 or higher,
   for lower degree polynomials use @{const roots1} or @{const croots2}\<close>

hide_const (open) eq

primrec remdups_gen :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_gen eq [] = []"
| "remdups_gen eq (x # xs) = (if (\<exists> y \<in> set xs. eq x y) then 
     remdups_gen eq xs else x # remdups_gen eq xs)"

  
lemma real_of_3_remdups_equal_3[simp]: "real_of_3 ` set (remdups_gen equal_3 xs) = real_of_3 ` set xs" 
  by (induct xs, auto simp: equal_3)
  
lemma distinct_remdups_equal_3: "distinct (map real_of_3 (remdups_gen equal_3 xs))"
  by (induct xs, auto, auto simp: equal_3)
  
lemma real_of_3_code [code]: "real_of_3 x = real_of (Real_Alg_Quotient x)" 
  by (transfer, auto)
    
definition "real_parts_3 p = roots_of_3 (root_poly_Re p)" 
  
definition "pos_imaginary_parts_3 p = 
  remdups_gen equal_3 (filter (\<lambda> x. sgn_3 x = 1) (concat (map roots_of_3 (root_poly_Im p))))" 

lemma real_parts_3: assumes p: "p \<noteq> 0" and "ipoly p x = 0" 
  shows "Re x \<in> real_of_3 ` set (real_parts_3 p)" 
  unfolding real_parts_3_def using represents_root_poly(1)[OF assms(2,1)]
    roots_of_3(1) unfolding represents_def by auto
    
lemma distinct_real_parts_3: "distinct (map real_of_3 (real_parts_3 p))" 
  unfolding real_parts_3_def using roots_of_3(2) .

lemma pos_imaginary_parts_3: assumes p: "p \<noteq> 0" and "ipoly p x = 0" and "Im x > 0" 
  shows "Im x \<in> real_of_3 ` set (pos_imaginary_parts_3 p)" 
proof -
  from represents_root_poly(2)[OF assms(2,1)] obtain q where 
    q: "q \<in> set (root_poly_Im p)" "q represents Im x" by auto
  from roots_of_3(1)[of q] have "Im x \<in> real_of_3 ` set (roots_of_3 q)" using q
    unfolding represents_def by auto
  then obtain i3 where i3: "i3 \<in> set (roots_of_3 q)" and id: "Im x = real_of_3 i3" by auto
  from \<open>Im x > 0\<close> have "sgn (Im x) = 1" by simp
  hence sgn: "sgn_3 i3 = 1" unfolding id by (metis of_rat_eq_1_iff sgn_3)
  show ?thesis unfolding pos_imaginary_parts_3_def real_of_3_remdups_equal_3 id
    using sgn i3 q(1) by auto
qed
  
lemma distinct_pos_imaginary_parts_3: "distinct (map real_of_3 (pos_imaginary_parts_3 p))" 
  unfolding pos_imaginary_parts_3_def by (rule distinct_remdups_equal_3)

lemma remdups_gen_subset: "set (remdups_gen eq xs) \<subseteq> set xs" 
  by (induct xs, auto)
    
lemma positive_pos_imaginary_parts_3: assumes "x \<in> set (pos_imaginary_parts_3 p)"
  shows "0 < real_of_3 x" 
proof -
  from subsetD[OF remdups_gen_subset assms[unfolded pos_imaginary_parts_3_def]]
  have "sgn_3 x = 1" by auto
  thus ?thesis using sgn_3[of x] by (simp add: sgn_1_pos)
qed
    
definition "pair_to_complex ri \<equiv> case ri of (r,i) \<Rightarrow> Complex (real_of_3 r) (real_of_3 i)" 
  
fun get_itvl_2 :: "real_alg_2 \<Rightarrow> real interval" where
  "get_itvl_2 (Irrational n (p,l,r)) = Interval (of_rat l) (of_rat r)" 
| "get_itvl_2 (Rational r) = (let rr = of_rat r in Interval rr rr)" 

lemma get_bounds_2: assumes "invariant_2 x"
  shows "real_of_2 x \<in>\<^sub>i get_itvl_2 x" 
proof (cases x)
  case (Irrational n plr)
  with assms obtain p l r where plr: "plr = (p,l,r)" by (cases plr, auto)
  from assms Irrational plr have inv1: "invariant_1 (p,l,r)" 
    and id: "real_of_2 x = real_of_1 (p,l,r)" by auto
  show ?thesis unfolding id using invariant_1D(1)[OF inv1] by (auto simp: plr Irrational)
qed (insert assms, auto simp: Let_def)

lift_definition get_itvl_3 :: "real_alg_3 \<Rightarrow> real interval" is get_itvl_2 .

lemma get_itvl_3: "real_of_3 x \<in>\<^sub>i get_itvl_3 x" 
  by (transfer, insert get_bounds_2, auto)

fun tighten_bounds_2 :: "real_alg_2 \<Rightarrow> real_alg_2" where
  "tighten_bounds_2 (Irrational n (p,l,r)) = (case tighten_poly_bounds p l r (sgn (ipoly p r))
    of (l',r',_) \<Rightarrow> Irrational n (p,l',r'))" 
| "tighten_bounds_2 (Rational r) = Rational r" 

lemma tighten_bounds_2: assumes inv: "invariant_2 x" 
  shows "real_of_2 (tighten_bounds_2 x) = real_of_2 x" "invariant_2 (tighten_bounds_2 x)" 
  "get_itvl_2 x = Interval l r \<Longrightarrow>
   get_itvl_2 (tighten_bounds_2 x) = Interval l' r' \<Longrightarrow> r' - l' = (r-l) / 2" 
proof (atomize(full), cases x)
  case (Irrational n plr)
  show "real_of_2 (tighten_bounds_2 x) = real_of_2 x \<and>
       invariant_2 (tighten_bounds_2 x) \<and>
       (get_itvl_2 x = Interval l r \<longrightarrow>
        get_itvl_2 (tighten_bounds_2 x) = Interval l' r' \<longrightarrow> r' - l' = (r - l) / 2)"
  proof -
    obtain p l r where plr: "plr = (p,l,r)" by (cases plr, auto)
    let ?tb = "tighten_poly_bounds p l r (sgn (ipoly p r))" 
    obtain l' r' sr' where tb: "?tb = (l',r',sr')" by (cases ?tb, auto)
    have id: "tighten_bounds_2 x = Irrational n (p,l',r')" unfolding Irrational plr
      using tb by auto
    from inv[unfolded Irrational plr] have inv: "invariant_1_2 (p, l, r)"
      "n = card {y. y \<le> real_of_1 (p, l, r) \<and> ipoly p y = 0}" by auto
    have rof: "real_of_2 x = real_of_1 (p, l, r)" 
      "real_of_2 (tighten_bounds_2 x) = real_of_1 (p, l', r')" using Irrational plr id by auto
    from inv have inv1: "invariant_1 (p, l, r)" and "poly_cond2 p" by auto
    hence rc: "\<exists>!x. root_cond (p, l, r) x" "poly_cond2 p" by auto
    note tb' = tighten_poly_bounds[OF tb rc refl]    
    have eq: "real_of_1 (p, l, r) = real_of_1 (p, l', r')" using tb' inv1
      using invariant_1_sub_interval(2) by presburger
    from inv1 tb' have "invariant_1 (p, l', r')" by (metis invariant_1_sub_interval(1))
    hence inv2: "invariant_2 (tighten_bounds_2 x)" unfolding id using inv eq by auto
    thus ?thesis unfolding rof eq unfolding id unfolding Irrational plr 
      using tb'(1-4) arg_cong[OF tb'(5), of real_of_rat] by (auto simp: hom_distribs)
  qed
qed (auto simp: Let_def)

lift_definition tighten_bounds_3 :: "real_alg_3 \<Rightarrow> real_alg_3" is tighten_bounds_2
  using tighten_bounds_2 by auto
    
lemma tighten_bounds_3:  
  "real_of_3 (tighten_bounds_3 x) = real_of_3 x"  
  "get_itvl_3 x = Interval l r \<Longrightarrow>
   get_itvl_3 (tighten_bounds_3 x) = Interval l' r' \<Longrightarrow> r' - l' = (r-l) / 2" 
  by (transfer, insert tighten_bounds_2, auto)+
    
partial_function (tailrec) filter_list_length 
  :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  [code]: "filter_list_length f p n xs = (let ys = filter p xs 
     in if length ys = n then ys else
     filter_list_length f p n (map f ys))"

lemma filter_list_length: assumes "length (filter P xs) = n"
  and "\<And> i x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> p ((f ^^ i) x)" 
  and "\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> \<exists> i. \<not> p ((f ^^ i) x)" 
  and g: "\<And> x. g (f x) = g x"
  and P: "\<And> x. P (f x) = P x" 
shows "map g (filter_list_length f p n xs) = map g (filter P xs)" 
proof -
  from assms(3) have "\<forall> x. \<exists> i. x \<in> set xs \<longrightarrow> \<not> P x \<longrightarrow> \<not> p ((f ^^ i) x)" 
    by auto
  from choice[OF this] obtain i where i: "\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> \<not> p ((f ^^ (i x)) x)"  
    by auto
  define m where "m = max_list (map i xs)" 
  have m: "\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> \<exists> i \<le> m. \<not> p ((f ^^ i) x)"
    using max_list[of _ "map i xs", folded m_def] i by auto
  show ?thesis using assms(1-2) m
  proof (induct m arbitrary: xs rule: less_induct)
    case (less m xs)
    define ys where "ys = filter p xs"       
    have xs_ys: "filter P xs = filter P ys" unfolding ys_def filter_filter
      by (rule filter_cong[OF refl], insert less(3)[of _ 0], auto)    
    have "filter (P \<circ> f) ys = filter P ys" using P unfolding o_def by auto
    hence id3: "filter P (map f ys) = map f (filter P ys)" unfolding filter_map by simp      
    hence id2: "map g (filter P (map f ys)) = map g (filter P ys)" by (simp add: g)
    show ?case 
    proof (cases "length ys = n")
      case True
      hence id: "filter_list_length f p n xs = ys" unfolding ys_def 
        filter_list_length.simps[of _ _ _ xs] Let_def by auto 
      show ?thesis using True unfolding id xs_ys using less(2)
        by (metis filter_id_conv length_filter_less less_le xs_ys) 
    next
      case False
      {
        assume "m = 0" 
        from less(4)[unfolded this] have Pp: "x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> \<not> p x" for x by auto
        with xs_ys False[folded less(2)] have False
          by (metis (mono_tags, lifting) filter_True mem_Collect_eq set_filter ys_def)
      } note m0 = this
      then obtain M where mM: "m = Suc M" by (cases m, auto)
      hence m: "M < m" by simp
      from False have id: "filter_list_length f p n xs = filter_list_length f p n (map f ys)" 
        unfolding ys_def filter_list_length.simps[of _ _ _ xs] Let_def by auto
      show ?thesis unfolding id xs_ys id2[symmetric]
      proof (rule less(1)[OF m])
        fix y
        assume "y \<in> set (map f ys)" 
        then obtain x where x: "x \<in> set xs" "p x" and y: "y = f x" unfolding ys_def by auto
        {
          assume "\<not> P y"
          hence "\<not> P x" unfolding y P .
          from less(4)[OF x(1) this] obtain i where i: "i \<le> m" and p: "\<not> p ((f ^^ i) x)" by auto
          with x obtain j where ij: "i = Suc j" by (cases i, auto)
          with i have j: "j \<le> M" unfolding mM by auto
          have "\<not> p ((f ^^ j) y)" using p unfolding ij y funpow_Suc_right by simp
          thus "\<exists>i\<le> M. \<not> p ((f ^^ i) y)" using j by auto
        }
        {
          fix i
          assume "P y" 
          hence "P x" unfolding y P .
          from less(3)[OF x(1) this, of "Suc i"]
          show "p ((f ^^ i) y)" unfolding y funpow_Suc_right by simp
        }
      next
        show "length (filter P (map f ys)) = n" unfolding id3 length_map using xs_ys less(2) by auto
      qed
    qed
  qed
qed


definition complex_roots_of_int_poly3 :: "int poly \<Rightarrow> complex list" where
  "complex_roots_of_int_poly3 p \<equiv> let n = degree p; 
    rrts = real_roots_of_int_poly p;
    nr = length rrts; 
    crts = map (\<lambda> r. Complex r 0) rrts
    in 
    if n = nr then crts 
    else let nr_crts = n - nr in if nr_crts = 2 then 
    let pp = real_of_int_poly p div (prod_list (map (\<lambda> x. [:-x,1:]) rrts));
        cpp = map_poly (\<lambda> r. Complex r 0) pp
      in crts @ croots2 cpp else
    let
        nr_pos_crts = nr_crts div 2;
        rxs = real_parts_3 p;
        ixs = pos_imaginary_parts_3 p;
        rts = [(rx, ix). rx <- rxs, ix <- ixs];
        crts' = map pair_to_complex 
           (filter_list_length (map_prod tighten_bounds_3 tighten_bounds_3) 
              (\<lambda> (r, i). 0 \<in>\<^sub>c ipoly_complex_interval p (Complex_Interval (get_itvl_3 r) (get_itvl_3 i))) nr_pos_crts rts)
    in crts @ (concat (map (\<lambda> x. [x, cnj x]) crts'))"

definition complex_roots_of_int_poly_all :: "int poly \<Rightarrow> complex list" where
  "complex_roots_of_int_poly_all p = (let n = degree p in 
    if n \<ge> 3 then complex_roots_of_int_poly3 p
    else if n = 1 then [roots1 (map_poly of_int p)] else if n = 2 then croots2 (map_poly of_int p)
    else [])"

lemma in_real_itvl_get_bounds_tighten: "real_of_3 x \<in>\<^sub>i get_itvl_3 ((tighten_bounds_3 ^^ n) x)" 
proof (induct n arbitrary: x)
  case 0
  thus ?case using get_itvl_3[of x] by simp
next
  case (Suc n x)
  have id: "(tighten_bounds_3 ^^ (Suc n)) x = (tighten_bounds_3 ^^ n) (tighten_bounds_3 x)"
    by (metis comp_apply funpow_Suc_right)
  show ?case unfolding id tighten_bounds_3(1)[of x, symmetric] by (rule Suc)
qed


lemma sandwitch_real:
 fixes l r :: "nat \<Rightarrow> real"
 assumes la: "l \<longlonglongrightarrow> a" and ra: "r \<longlonglongrightarrow> a"
 and lm: "\<And>i. l i \<le> m i" and mr: "\<And>i. m i \<le> r i"
shows "m \<longlonglongrightarrow> a"
proof (rule LIMSEQ_I)
  fix e :: real
  assume "0 < e"
  hence e: "0 < e / 2" by simp  
  from LIMSEQ_D[OF la e] obtain n1 where n1: "\<And> n. n \<ge> n1 \<Longrightarrow> norm (l n - a) < e/2" by auto
  from LIMSEQ_D[OF ra e] obtain n2 where n2: "\<And> n. n \<ge> n2 \<Longrightarrow> norm (r n - a) < e/2" by auto
  show "\<exists>no. \<forall>n\<ge>no. norm (m n - a) < e"
  proof (rule exI[of _ "max n1 n2"], intro allI impI)  
    fix n
    assume "max n1 n2 \<le> n"     
    with n1 n2 have *: "norm (l n - a) < e/2" "norm (r n - a) < e/2" by auto
    from lm[of n] mr[of n] have "norm (m n - a) \<le> norm (l n - a) + norm (r n - a)" by simp
    with * show "norm (m n - a) < e" by auto
  qed
qed

lemma real_of_tighten_bounds_many[simp]: "real_of_3 ((tighten_bounds_3 ^^ i) x) = real_of_3 x"
  apply (induct i) using tighten_bounds_3 by auto

definition lower_3 where "lower_3 x i \<equiv> interval.lower (get_itvl_3 ((tighten_bounds_3 ^^ i) x))"
definition upper_3 where "upper_3 x i \<equiv> interval.upper (get_itvl_3 ((tighten_bounds_3 ^^ i) x))"

lemma interval_size_3: "upper_3 x i - lower_3 x i = (upper_3 x 0 - lower_3 x 0)/2^i"
proof (induct i)
  case (Suc i)
  have "upper_3 x (Suc i) - lower_3 x (Suc i) = (upper_3 x i - lower_3 x i) / 2"
     unfolding upper_3_def lower_3_def using tighten_bounds_3 get_itvl_3 by auto
  with Suc show ?case by auto
qed auto

lemma interval_size_3_tendsto_0: "(\<lambda>i. (upper_3 x i - lower_3 x i)) \<longlonglongrightarrow> 0"
  by (subst interval_size_3, auto intro: LIMSEQ_divide_realpow_zero)

lemma dist_tendsto_0_imp_tendsto: "(\<lambda>i. \<bar>f i - a\<bar> :: real) \<longlonglongrightarrow> 0 \<Longrightarrow> f \<longlonglongrightarrow> a"
  using LIM_zero_cancel tendsto_rabs_zero_iff by blast

lemma upper_3_tendsto: "upper_3 x \<longlonglongrightarrow> real_of_3 x"
proof(rule dist_tendsto_0_imp_tendsto, rule sandwitch_real)
  fix i
  obtain l r where lr: "get_itvl_3 ((tighten_bounds_3 ^^ i) x) = Interval l r"
    by (metis interval.collapse)
  with get_itvl_3[of "(tighten_bounds_3 ^^ i) x"]
  show "\<bar>(upper_3 x) i - real_of_3 x\<bar> \<le> (upper_3 x i - lower_3 x i)"
    unfolding upper_3_def lower_3_def by auto
qed (insert interval_size_3_tendsto_0, auto)

lemma lower_3_tendsto: "lower_3 x \<longlonglongrightarrow> real_of_3 x"
proof(rule dist_tendsto_0_imp_tendsto, rule sandwitch_real)
  fix i
  obtain l r where lr: "get_itvl_3 ((tighten_bounds_3 ^^ i) x) = Interval l r"
    by (metis interval.collapse)
  with get_itvl_3[of "(tighten_bounds_3 ^^ i) x"]
  show "\<bar>lower_3 x i - real_of_3 x\<bar> \<le> (upper_3 x i - lower_3 x i)"
    unfolding upper_3_def lower_3_def by auto
qed (insert interval_size_3_tendsto_0, auto)

lemma tends_to_tight_bounds_3: "(\<lambda>x. get_itvl_3 ((tighten_bounds_3 ^^ x) y)) \<longlonglongrightarrow>\<^sub>i real_of_3 y" 
  using lower_3_tendsto[of y] upper_3_tendsto[of y] unfolding lower_3_def upper_3_def
    interval_tendsto_def o_def by auto
    
lemma complex_roots_of_int_poly3: assumes p: "p \<noteq> 0" and sf: "square_free p" 
  shows "set (complex_roots_of_int_poly3 p) = {x. ipoly p x = 0}" (is "?l = ?r")
    "distinct (complex_roots_of_int_poly3 p)" 
proof -
  interpret map_poly_inj_idom_hom of_real..
  define q where "q = real_of_int_poly p"
  let ?q = "map_poly complex_of_real q"
  from p have q0: "q \<noteq> 0" unfolding q_def by auto
  hence q: "?q \<noteq> 0" by auto
  define rr where "rr = real_roots_of_int_poly p"
  define rrts where "rrts = map (\<lambda>r. Complex r 0) rr"
  note d = complex_roots_of_int_poly3_def[of p, unfolded Let_def, folded rr_def, folded rrts_def]
  have rr: "set rr = {x. ipoly p x = 0}" unfolding rr_def
    using real_roots_of_int_poly(1)[OF p] .
  have rrts: "set rrts = {x. poly ?q x = 0 \<and> x \<in> \<real>}" unfolding rrts_def set_map rr q_def
    complex_of_real_def[symmetric] by (auto elim: Reals_cases)
  have dist: "distinct rr" unfolding rr_def using real_roots_of_int_poly(2) .
  from dist have dist1: "distinct rrts" unfolding rrts_def distinct_map inj_on_def by auto
  have lrr: "length rr = card {x. poly (real_of_int_poly p) x = 0}"
    unfolding rr_def using real_roots_of_int_poly[of p] p distinct_card by fastforce
  have cr: "length rr = card {x. poly ?q x = 0 \<and> x \<in> \<real>}" unfolding lrr q_def[symmetric]
  proof -
    have "card {x. poly q x = 0} \<le> card {x. poly (map_poly complex_of_real q) x = 0 \<and> x \<in> \<real>}" (is "?l \<le> ?r")
      by (rule card_inj_on_le[of of_real], insert poly_roots_finite[OF q], auto simp: inj_on_def)
    moreover have "?l \<ge> ?r"
      by (rule card_inj_on_le[of Re, OF _ _ poly_roots_finite[OF q0]], auto simp: inj_on_def elim!: Reals_cases)
    ultimately show "?l = ?r" by simp
  qed 
  have conv: "\<And> x. ipoly p x = 0 \<longleftrightarrow> poly ?q x = 0"
    unfolding q_def by (subst map_poly_map_poly, auto simp: o_def)
  have r: "?r = {x. poly ?q x = 0}" unfolding conv ..
  have "?l = {x. ipoly p x = 0} \<and> distinct (complex_roots_of_int_poly3 p)" 
  proof (cases "degree p = length rr")
    case False note oFalse = this
    show ?thesis
    proof (cases "degree p - length rr = 2")
      case False
      let ?nr = "(degree p - length rr) div 2" 
      define cpxI where "cpxI = pos_imaginary_parts_3 p" 
      define cpxR where "cpxR = real_parts_3 p" 
      let ?rts = "[(rx,ix). rx <- cpxR, ix <- cpxI]" 
      define cpx where "cpx = map pair_to_complex (filter (\<lambda> c. ipoly p (pair_to_complex c) = 0) 
         ?rts)"
      let ?LL = "cpx @ map cnj cpx" 
      let ?LL' = "concat (map (\<lambda> x. [x,cnj x]) cpx)" 
      let ?ll = "rrts @ ?LL" 
      let ?ll' = "rrts @ ?LL'" 
      have cpx: "set cpx \<subseteq> ?r" unfolding cpx_def by auto
      have ccpx: "cnj ` set cpx \<subseteq> ?r" using cpx unfolding r 
        by (auto intro!: complex_conjugate_root[of ?q] simp: Reals_def) 
      have "set ?ll \<subseteq> ?r" using rrts cpx ccpx unfolding r by auto
      moreover
      {
        fix x :: complex
        assume rt: "ipoly p x = 0"
        {
          fix x 
          assume rt: "ipoly p x = 0"
            and gt: "Im x > 0"
          define rx where "rx = Re x"
          let ?x = "Complex rx (Im x)"
          have x: "x = ?x" by (cases x, auto simp: rx_def)
          from rt x have rt': "ipoly p ?x = 0" by auto
          from real_parts_3[OF p rt, folded rx_def] pos_imaginary_parts_3[OF p rt gt] rt'
          have "?x \<in> set cpx" unfolding cpx_def cpxI_def cpxR_def 
            by (force simp: pair_to_complex_def[abs_def])
          hence "x \<in> set cpx" using x by simp
        } note gt = this
        have cases: "Im x = 0 \<or> Im x > 0 \<or> Im x < 0" by auto
        from rt have rt': "ipoly p (cnj x) = 0" unfolding conv 
          by (intro complex_conjugate_root[of ?q x], auto simp: Reals_def)
        {
          assume "Im x > 0"
          from gt[OF rt this] have "x \<in> set ?ll" by auto
        }
        moreover
        {
          assume "Im x < 0"
          hence "Im (cnj x) > 0" by simp
          from gt[OF rt' this] have "cnj (cnj x) \<in> set ?ll" unfolding set_append set_map by blast
          hence "x \<in> set ?ll" by simp
        }
        moreover
        {
          assume "Im x = 0"
          hence "x \<in> \<real>" using complex_is_Real_iff by blast
          with rt rrts have "x \<in> set ?ll" unfolding conv by auto
        }
        ultimately have "x \<in> set ?ll" using cases by blast
      }
      ultimately have lr: "set ?ll = {x. ipoly p x = 0}" by blast 
      let ?rr = "map real_of_3 cpxR" 
      let ?pi = "map real_of_3 cpxI" 
      have dist2: "distinct ?rr" unfolding cpxR_def by (rule distinct_real_parts_3)
      have dist3: "distinct ?pi" unfolding cpxI_def by (rule distinct_pos_imaginary_parts_3)
      have idd: "concat (map (map pair_to_complex) (map (\<lambda>rx. map (Pair rx) cpxI) cpxR))
        = concat (map (\<lambda>r. map (\<lambda> i. Complex (real_of_3 r) (real_of_3 i)) cpxI) cpxR)" 
        unfolding pair_to_complex_def by (auto simp: o_def)
      have dist4: "distinct cpx" unfolding cpx_def 
      proof (rule distinct_map_filter, unfold map_concat idd, unfold distinct_conv_nth, intro allI impI, goal_cases) 
        case (1 i j)
        from nth_concat_diff[OF 1, unfolded length_map] dist2[unfolded distinct_conv_nth]
         dist3[unfolded distinct_conv_nth] show ?case by auto
      qed
      have dist5: "distinct (map cnj cpx)" using dist4 unfolding distinct_map by (auto simp: inj_on_def)
      {
        fix x :: complex
        have rrts: "x \<in> set rrts \<Longrightarrow> Im x = 0" unfolding rrts_def by auto
        have cpx: "\<And> x. x \<in> set cpx \<Longrightarrow> Im x > 0" unfolding cpx_def cpxI_def
          by (auto simp: pair_to_complex_def[abs_def] positive_pos_imaginary_parts_3)
        have cpx': "x \<in> cnj ` set cpx \<Longrightarrow> sgn (Im x) = -1" using cpx by auto
        have "x \<notin> set rrts \<inter> set cpx \<union> set rrts \<inter> cnj ` set cpx \<union> set cpx \<inter> cnj ` set cpx" 
          using rrts cpx[of x] cpx' by auto
      } note dist6 = this
      have dist: "distinct ?ll" 
        unfolding distinct_append using dist6 by (auto simp: dist1 dist4 dist5)
      let ?p = "complex_of_int_poly p" 
      have pp: "?p \<noteq> 0" using p by auto
      from p square_free_of_int_poly[OF sf] square_free_rsquarefree
      have rsf:"rsquarefree ?p" by auto
      from dist lr have "length ?ll = card {x. poly ?p x = 0}"
        by (metis distinct_card)
      also have "\<dots> = degree p" 
        using rsf unfolding rsquarefree_card_degree[OF pp] by simp
      finally have deg_len: "degree p = length ?ll" by simp
      let ?P = "\<lambda> c.  ipoly p (pair_to_complex c) = 0" 
      let ?itvl = "\<lambda> r i. ipoly_complex_interval p (Complex_Interval (get_itvl_3 r) (get_itvl_3 i))" 
      let ?itv = "\<lambda> (r,i). ?itvl r i" 
      let ?p = "(\<lambda> (r,i). 0 \<in>\<^sub>c (?itvl r i))" 
      let ?tb = tighten_bounds_3  
      let ?f = "map_prod ?tb ?tb" 
      have filter: "map pair_to_complex (filter_list_length ?f ?p ?nr ?rts) = map pair_to_complex (filter ?P ?rts)" 
      proof (rule filter_list_length)
        have "length (filter ?P ?rts) = length cpx" 
          unfolding cpx_def by simp
        also have "\<dots> = ?nr" unfolding deg_len by (simp add: rrts_def)
        finally show "length (filter ?P ?rts) = ?nr" by auto
      next
        fix n x
        assume x: "?P x" 
        obtain r i where xri: "x = (r,i)" by force
        have id: "(?f ^^ n) x = ((?tb ^^ n) r, (?tb ^^ n) i)" unfolding xri
          by (induct n, auto)
        have px: "pair_to_complex x = Complex (real_of_3 r) (real_of_3 i)" 
          unfolding xri pair_to_complex_def by auto
        show "?p ((?f ^^ n) x)"
          unfolding id split 
          by (rule ipoly_complex_interval[of "pair_to_complex x" _ p, unfolded x], unfold px,
            auto simp: in_complex_interval_def in_real_itvl_get_bounds_tighten)
      next
        fix x
        assume x: "x \<in> set ?rts" "\<not> ?P x"
        let ?x = "pair_to_complex x" 
        obtain r i where xri: "x = (r,i)" by force
        have id: "(?f ^^ n) x = ((?tb ^^ n) r, (?tb ^^ n) i)" for n unfolding xri
          by (induct n, auto)
        have px: "?x = Complex (real_of_3 r) (real_of_3 i)" 
          unfolding xri pair_to_complex_def by auto
        have cvg: "(\<lambda> n. ?itv ((?f ^^ n) x)) \<longlonglongrightarrow>\<^sub>c ipoly p ?x" 
          unfolding id split px
        proof (rule ipoly_complex_interval_tendsto)
          show "(\<lambda>ia. Complex_Interval (get_itvl_3 ((?tb ^^ ia) r)) (get_itvl_3 ((?tb ^^ ia) i))) \<longlonglongrightarrow>\<^sub>c
            Complex (real_of_3 r) (real_of_3 i)" 
            unfolding complex_interval_tendsto_def by (simp add: tends_to_tight_bounds_3 o_def)
        qed
        from complex_interval_tendsto_neq[OF this x(2)]
        show "\<exists> i. \<not> ?p ((?f ^^ i) x)" unfolding id by auto
      next
        show "pair_to_complex (?f x) = pair_to_complex x" for x
          by (cases x, auto simp: pair_to_complex_def tighten_bounds_3(1))
      next
        show "?P (?f x) = ?P x" for x 
          by (cases x, auto simp: pair_to_complex_def tighten_bounds_3(1)) 
      qed
      have l: "complex_roots_of_int_poly3 p = ?ll'" 
        unfolding d filter cpx_def[symmetric] cpxI_def[symmetric] cpxR_def[symmetric] using False oFalse
        by auto   
      have "distinct ?ll' = (distinct rrts \<and> distinct ?LL' \<and> set rrts \<inter> set ?LL' = {})" 
        unfolding distinct_append ..
      also have "set ?LL' = set ?LL" by auto
      also have "distinct ?LL' = distinct ?LL" by (induct cpx, auto)
      finally have "distinct ?ll' = distinct ?ll" unfolding distinct_append by auto
      with dist have "distinct ?ll'" by auto
      with lr l show ?thesis by auto
    next
      case True
      let ?cr = "map_poly of_real :: real poly \<Rightarrow> complex poly"
      define pp where "pp = complex_of_int_poly p"
      have id: "pp = map_poly of_real q" unfolding q_def pp_def
        by (subst map_poly_map_poly, auto simp: o_def)
      let ?rts = "map (\<lambda> x. [:-x,1:]) rr"
      define rts where "rts = prod_list ?rts"
      let ?c2 = "?cr (q div rts)"
      have pq: "\<And> x. ipoly p x = 0 \<longleftrightarrow> poly q x = 0" unfolding q_def by simp
      from True have 2: "degree q - card {x. poly q x = 0} = 2" unfolding pq[symmetric] lrr
        unfolding q_def by simp
      from True have id: "degree p = length rr \<longleftrightarrow> False" 
        "degree p - length rr = 2 \<longleftrightarrow> True" by auto
      have l: "?l = of_real ` {x. poly q x = 0} \<union> set (croots2 ?c2)"
        unfolding d rts_def id if_False if_True set_append rrts Reals_def
        by (fold complex_of_real_def q_def, auto)
      from dist
      have len_rr: "length rr = card {x. poly q x = 0}" unfolding rr[unfolded pq, symmetric] 
        by (simp add: distinct_card)
      have rr': "\<And> r. r \<in> set rr \<Longrightarrow> poly q r = 0" using rr unfolding q_def by simp
      with dist have "q = q div prod_list ?rts * prod_list ?rts"
      proof (induct rr arbitrary: q)
        case (Cons r rr q)
        note dist = Cons(2)
        let ?p = "q div [:-r,1:]"
        from Cons.prems(2) have "poly q r = 0" by simp
        hence "[:-r,1:] dvd q" using poly_eq_0_iff_dvd by blast
        from dvd_mult_div_cancel[OF this]
        have "q = ?p * [:-r,1:]" by simp
        moreover have "?p = ?p div (\<Prod>x\<leftarrow>rr. [:- x, 1:]) * (\<Prod>x\<leftarrow>rr. [:- x, 1:])"
        proof (rule Cons.hyps)
          show "distinct rr" using dist by auto
          fix s
          assume "s \<in> set rr"
          with dist Cons(3) have "s \<noteq> r" "poly q s = 0" by auto
          hence "poly (?p * [:- 1 * r, 1:]) s = 0" using calculation by force
          thus "poly ?p s = 0" by (simp add: \<open>s \<noteq> r\<close>)
        qed
        ultimately have q: "q = ?p div (\<Prod>x\<leftarrow>rr. [:- x, 1:]) * (\<Prod>x\<leftarrow>rr. [:- x, 1:]) * [:-r,1:]"
          by auto
        also have "\<dots> = (?p div (\<Prod>x\<leftarrow>rr. [:- x, 1:])) * (\<Prod>x\<leftarrow>r # rr. [:- x, 1:])"
          unfolding mult.assoc by simp
        also have "?p div (\<Prod>x\<leftarrow>rr. [:- x, 1:]) = q div (\<Prod>x\<leftarrow>r # rr. [:- x, 1:])"
          unfolding poly_div_mult_right[symmetric] by simp
        finally show ?case .
      qed simp
      hence q_div: "q = q div rts * rts" unfolding rts_def .
      from q_div q0 have "q div rts \<noteq> 0" "rts \<noteq> 0" by auto
      from degree_mult_eq[OF this] have "degree q = degree (q div rts) + degree rts"
        using q_div by simp
      also have "degree rts = length rr" unfolding rts_def by (rule degree_linear_factors)
      also have "\<dots> = card {x. poly q x = 0}" unfolding len_rr by simp
      finally have deg2: "degree ?c2 = 2" using 2 by simp
      note croots2 = croots2[OF deg2, symmetric]
      have "?q = ?cr (q div rts * rts)" using q_div by simp
      also have "\<dots> = ?cr rts * ?c2" unfolding hom_distribs by simp
      finally have q_prod: "?q = ?cr rts * ?c2" .
      from croots2 l
      have l: "?l = of_real ` {x. poly q x = 0} \<union> {x. poly ?c2 x = 0}" by simp
      from r[unfolded q_prod]
      have r: "?r = {x. poly (?cr rts) x = 0} \<union> {x. poly ?c2 x = 0}" by auto
      also have "?cr rts = (\<Prod>x\<leftarrow>rr. ?cr [:- x, 1:])" by (simp add: rts_def o_def of_real_poly_hom.hom_prod_list)
      also have "{x. poly \<dots> x = 0} = of_real ` set rr" 
        unfolding poly_prod_list_zero_iff by auto
      also have "set rr = {x. poly q x = 0}" unfolding rr q_def by simp
      finally have lr: "?l = ?r" unfolding l by simp
      show ?thesis 
      proof (intro conjI[OF lr])
        from sf have sf: "square_free q" unfolding q_def by (rule square_free_of_int_poly)
        {
          interpret field_hom_0' complex_of_real ..
          from sf have "square_free ?q" unfolding square_free_map_poly .
        } note sf = this
        have l: "complex_roots_of_int_poly3 p = rrts @ croots2 ?c2" 
          unfolding d rts_def id if_False if_True set_append rrts q_def complex_of_real_def by auto
        have dist2: "distinct (croots2 ?c2)" unfolding croots2_def Let_def by auto        
        {
          fix x
          assume x: "x \<in> set (croots2 ?c2)" "x \<in> set rrts" 
          from x(1)[unfolded croots2] have x1: "poly ?c2 x = 0" by auto
          from x(2) have x2: "poly (?cr rts) x = 0" 
            unfolding rrts_def rts_def complex_of_real_def[symmetric]
            by (auto simp: poly_prod_list_zero_iff o_def) 
          from square_free_multD(1)[OF sf[unfolded q_prod], of "[: -x, 1:]"]
            x1 x2 have False unfolding poly_eq_0_iff_dvd by auto 
        } note dist3 = this
        show "distinct (complex_roots_of_int_poly3 p)" unfolding l distinct_append
          by (intro conjI dist1 dist2, insert dist3, auto)
      qed
    qed
  next
    case True
    have "card {x. poly ?q x = 0} \<le> degree ?q" by (rule poly_roots_degree[OF q])
    also have "\<dots> = degree p" unfolding q_def by simp
    also have "\<dots> = card {x. poly ?q x = 0 \<and> x \<in> \<real>}" using True cr by simp
    finally have le: "card {x. poly ?q x = 0} \<le> card {x. poly ?q x = 0 \<and> x \<in> \<real>}" by auto
    have "{x. poly ?q x = 0 \<and> x \<in> \<real>} = {x. poly ?q x = 0}"
      by (rule card_seteq[OF _ _ le], insert poly_roots_finite[OF q], auto)
    with True rrts dist1 show ?thesis unfolding r d by auto
  qed
  thus "distinct (complex_roots_of_int_poly3 p)" "?l = ?r" by auto
qed

lemma complex_roots_of_int_poly_all: assumes sf: "degree p \<ge> 3 \<Longrightarrow> square_free p" 
  shows "p \<noteq> 0 \<Longrightarrow> set (complex_roots_of_int_poly_all p) = {x. ipoly p x = 0}" (is "_ \<Longrightarrow> set ?l = ?r")
    and "distinct (complex_roots_of_int_poly_all p)" 
proof -
  note d = complex_roots_of_int_poly_all_def Let_def
  have "(p \<noteq> 0 \<longrightarrow> set ?l = ?r) \<and> (distinct (complex_roots_of_int_poly_all p))" 
  proof (cases "degree p \<ge> 3")
    case True
    hence p: "p \<noteq> 0" by auto
    from True complex_roots_of_int_poly3[OF p] sf show ?thesis unfolding d by auto
  next
    case False
    let ?p = "map_poly (of_int :: int \<Rightarrow> complex) p"
    have deg: "degree ?p = degree p" 
      by (simp add: degree_map_poly)
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence l: "?l = [roots1 ?p]" unfolding d by auto
      from True have "degree ?p = 1" unfolding deg by auto
      from roots1[OF this] show ?thesis unfolding l roots1_def by auto
    next
      case False
      show ?thesis 
      proof (cases "degree p = 2")
        case True
        hence l: "?l = croots2 ?p" unfolding d by auto
        from True have "degree ?p = 2" unfolding deg by auto
        from croots2[OF this] show ?thesis unfolding l by (simp add: croots2_def Let_def)
      next
        case False
        with \<open>degree p \<noteq> 1\<close> \<open>degree p \<noteq> 2\<close> \<open>\<not> (degree p \<ge> 3)\<close> have True: "degree p = 0" by auto
        hence l: "?l = []" unfolding d by auto
        from True have "degree ?p = 0" unfolding deg by auto
        from roots0[OF _ this] show ?thesis unfolding l by simp
      qed
    qed
  qed
  thus "p \<noteq> 0 \<Longrightarrow> set ?l = ?r" "distinct (complex_roots_of_int_poly_all p)" by auto
qed

text \<open>It now comes the preferred function to compute complex roots of a integer polynomial.\<close>
definition complex_roots_of_int_poly :: "int poly \<Rightarrow> complex list" where
  "complex_roots_of_int_poly p = (
    let ps = (if degree p \<ge> 3 then factors_of_int_poly p else [p])
    in concat (map complex_roots_of_int_poly_all ps))"

definition complex_roots_of_rat_poly :: "rat poly \<Rightarrow> complex list" where
  "complex_roots_of_rat_poly p = complex_roots_of_int_poly (snd (rat_to_int_poly p))"
 
  
lemma complex_roots_of_int_poly:
  shows "p \<noteq> 0 \<Longrightarrow> set (complex_roots_of_int_poly p) = {x. ipoly p x = 0}" (is "_ \<Longrightarrow> ?l = ?r")
  and "distinct (complex_roots_of_int_poly p)" 
proof -
  have "(p \<noteq> 0 \<longrightarrow> ?l = ?r) \<and> (distinct (complex_roots_of_int_poly p))" 
  proof (cases "degree p \<ge> 3")
    case False
    hence "complex_roots_of_int_poly p = complex_roots_of_int_poly_all p"
      unfolding complex_roots_of_int_poly_def Let_def by auto
    with complex_roots_of_int_poly_all[of p] False show ?thesis by auto
  next
    case True
    {
      fix q
      assume "q \<in> set (factors_of_int_poly p)"
      from factors_of_int_poly(1)[OF refl this] irreducible_imp_square_free[of q] 
      have 0: "q \<noteq> 0" and sf: "square_free q" by auto
      from complex_roots_of_int_poly_all(1)[OF sf 0] complex_roots_of_int_poly_all(2)[OF sf]
      have "set (complex_roots_of_int_poly_all q) = {x. ipoly q x = 0}" 
        "distinct (complex_roots_of_int_poly_all q)" by auto
    } note all = this
    from True have 
      "?l = (\<Union> ((\<lambda> p. set (complex_roots_of_int_poly_all p)) ` set (factors_of_int_poly p)))"
      unfolding complex_roots_of_int_poly_def Let_def by auto    
    also have "\<dots> = (\<Union> ((\<lambda> p. {x. ipoly p x = 0}) ` set (factors_of_int_poly p)))"
      using all by blast
    finally have l: "?l = (\<Union> ((\<lambda> p. {x. ipoly p x = 0}) ` set (factors_of_int_poly p)))" .    
    have lr: "p \<noteq> 0 \<longrightarrow> ?l = ?r" using l factors_of_int_poly(2)[OF refl, of p] by auto
    show ?thesis 
    proof (rule conjI[OF lr])
      from True have id: "complex_roots_of_int_poly p = 
          concat (map complex_roots_of_int_poly_all (factors_of_int_poly p))" 
        unfolding complex_roots_of_int_poly_def Let_def by auto
      show "distinct (complex_roots_of_int_poly p)" unfolding id distinct_conv_nth
      proof (intro allI impI, goal_cases)
        case (1 i j)
        let ?fp = "factors_of_int_poly p" 
        let ?rr = "complex_roots_of_int_poly_all" 
        let ?cc = "concat (map ?rr (factors_of_int_poly p))" 
        from nth_concat_diff[OF 1, unfolded length_map]
        obtain j1 k1 j2 k2 where 
          *: "(j1,k1) \<noteq> (j2,k2)"
          "j1 < length ?fp" "j2 < length ?fp" and
          "k1 < length (map ?rr ?fp ! j1)"
          "k2 < length (map ?rr ?fp ! j2)"
          "?cc ! i = map ?rr ?fp ! j1 ! k1" 
          "?cc ! j = map ?rr ?fp ! j2 ! k2" by blast
        hence **: "k1 < length (?rr (?fp ! j1))" 
          "k2 < length (?rr (?fp ! j2))" 
          "?cc ! i = ?rr (?fp ! j1) ! k1"
          "?cc ! j = ?rr (?fp ! j2) ! k2"
          by auto
        from * have mem: "?fp ! j1 \<in> set ?fp" "?fp ! j2 \<in> set ?fp" by auto
        show "?cc ! i \<noteq> ?cc ! j"
        proof (cases "j1 = j2")
          case True
          with * have "k1 \<noteq> k2" by auto
          with all(2)[OF mem(2)] **(1-2) show ?thesis unfolding **(3-4) unfolding True
            distinct_conv_nth by auto
        next
          case False
          from \<open>degree p \<ge> 3\<close> have p: "p \<noteq> 0" by auto
          note fip = factors_of_int_poly(2-3)[OF refl this]       
          show ?thesis unfolding **(3-4)
          proof
            define x where "x = ?rr (?fp ! j2) ! k2" 
            assume id: "?rr (?fp ! j1) ! k1 = ?rr (?fp ! j2) ! k2" 
            from ** have x1: "x \<in> set (?rr (?fp ! j1))" unfolding x_def id[symmetric] by auto
            from ** have x2: "x \<in> set (?rr (?fp ! j2))" unfolding x_def by auto            
            from all(1)[OF mem(1)] x1 have x1: "ipoly (?fp ! j1) x = 0" by auto
            from all(1)[OF mem(2)] x2 have x2: "ipoly (?fp ! j2) x = 0" by auto
            from False factors_of_int_poly(4)[OF refl, of p] have neq: "?fp ! j1 \<noteq> ?fp ! j2" 
              using * unfolding distinct_conv_nth by auto
            have "poly (complex_of_int_poly p) x = 0" by (meson fip(1) mem(2) x2)
            from fip(2)[OF this] mem x1 x2 neq
            show False by blast
          qed
        qed
      qed
    qed
  qed
  thus "p \<noteq> 0 \<Longrightarrow> ?l = ?r" "distinct (complex_roots_of_int_poly p)" by auto
qed

lemma complex_roots_of_rat_poly: 
  "p \<noteq> 0 \<Longrightarrow> set (complex_roots_of_rat_poly p) = {x. rpoly p x = 0}" (is "_ \<Longrightarrow> ?l = ?r")
  "distinct (complex_roots_of_rat_poly p)" 
proof -
  obtain c q where cq: "rat_to_int_poly p = (c,q)" by force
  from rat_to_int_poly[OF this]
  have pq: "p = smult (inverse (of_int c)) (of_int_poly q)" 
    and c: "c \<noteq> 0" by auto
  show "distinct (complex_roots_of_rat_poly p)" unfolding complex_roots_of_rat_poly_def
    using complex_roots_of_int_poly(2) .
  assume p: "p \<noteq> 0" 
  with pq c have q: "q \<noteq> 0" by auto
  have id: "{x. rpoly p x = (0 :: complex)} = {x. ipoly q x = 0}"
    unfolding pq by (simp add: c of_rat_of_int_poly hom_distribs)
  show "?l = ?r" unfolding complex_roots_of_rat_poly_def cq snd_conv id
    complex_roots_of_int_poly(1)[OF q] ..
qed

definition roots_of_complex_main :: "complex poly \<Rightarrow> complex list" where 
  "roots_of_complex_main p \<equiv> let n = degree p in 
    if n = 0 then [] else if n = 1 then [roots1 p] else if n = 2 then croots2 p
    else (complex_roots_of_rat_poly (map_poly to_rat p))"
  
definition roots_of_complex_poly :: "complex poly \<Rightarrow> complex list option" where
  "roots_of_complex_poly p \<equiv> let (c,pis) = yun_factorization gcd p in
    if (c \<noteq> 0 \<and> (\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (concat (map (roots_of_complex_main o fst) pis)) else None"

lemma roots_of_complex_main: assumes p: "p \<noteq> 0" and deg: "degree p \<le> 2 \<or> set (coeffs p) \<subseteq> \<rat>"
  shows "set (roots_of_complex_main p) = {x. poly p x = 0}" (is "set ?l = ?r")
    and "distinct (roots_of_complex_main p)" 
proof -
  note d = roots_of_complex_main_def Let_def
  have "set ?l = ?r \<and> distinct (roots_of_complex_main p)" 
  proof (cases "degree p = 0")
    case True
    hence "?l = []" unfolding d by auto
    with roots0[OF p True] show ?thesis by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?l = [roots1 p]" unfolding d by auto
      with roots1[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence "?l = croots2 p" unfolding d by auto
        with croots2[OF True] show ?thesis by (auto simp: croots2_def Let_def)
      next
        case False note 2 = this
        let ?q = "map_poly to_rat p"
        from 0 1 2 have l: "?l = complex_roots_of_rat_poly ?q" unfolding d by auto
        from deg 0 1 2 have rat: "set (coeffs p) \<subseteq> \<rat>" by auto
        have "p = map_poly (of_rat o to_rat) p"
          by (rule sym, rule map_poly_idI, insert rat, auto)
        also have "\<dots> = complex_of_rat_poly ?q"
          by (subst map_poly_map_poly, auto simp: to_rat)
        finally have id: "{x. poly p x = 0} = {x. poly (complex_of_rat_poly ?q) x = 0}" and q: "?q \<noteq> 0" 
          using p by auto
        from complex_roots_of_rat_poly[of ?q, folded id l] q
        show ?thesis by auto
      qed
    qed
  qed
  thus "set ?l = ?r" "distinct ?l" by auto
qed
 
lemma roots_of_complex_poly: assumes rt: "roots_of_complex_poly p = Some xs"
  shows "set xs = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization gcd p = (c,pis)" by force
  from rt[unfolded roots_of_complex_poly_def yun split Let_def]
  have c: "c \<noteq> 0" and pis: "\<And> p i. (p, i)\<in> set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xs: "xs = concat (map (roots_of_complex_main \<circ> fst) pis)"
    by (auto split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_prod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_complex_main p) = {x. poly p x = 0}"
      by (rule roots_of_complex_main, insert yun(2)[OF p] pis[OF p], auto)
  } note main = this
  have "set xs = \<Union> ((\<lambda> (p, i). set (roots_of_complex_main p)) ` set pis)" unfolding xs o_def
    by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

subsection \<open>Factorization of Complex Polynomials\<close>

definition factorize_complex_main :: "complex poly \<Rightarrow> (complex \<times> (complex \<times> nat) list) option" where
  "factorize_complex_main p \<equiv> let (c,pis) = yun_factorization gcd p in
    if ((\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (c, concat (map (\<lambda> (p,i). map (\<lambda> r. (r,i)) (roots_of_complex_main p)) pis)) else None"

definition factorize_complex_poly :: "complex poly \<Rightarrow> (complex \<times> (complex poly \<times> nat) list) option" where
  "factorize_complex_poly p \<equiv> map_option 
    (\<lambda> (c,ris). (c, map (\<lambda> (r,i). ([:-r,1:],Suc i)) ris)) (factorize_complex_main p)"


lemma factorize_complex_main: assumes rt: "factorize_complex_main p = Some (c,xis)"
  shows "p = smult c (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
proof -
  obtain d pis where yun: "yun_factorization gcd p = (d,pis)" by force
  from rt[unfolded factorize_complex_main_def yun split Let_def]
  have pis: "\<And> p i. (p, i)\<in>set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xis: "xis = concat (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (roots_of_complex_main p)) pis)"
    and d: "d = c"
    by (auto split: if_splits)
  note yun = yun_factorization[OF yun[unfolded d]]
  note yun = square_free_factorizationD[OF yun(1)] yun(2)[unfolded snd_conv]
  let ?exp = "\<lambda> pis. \<Prod>(x, i)\<leftarrow>concat
    (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (roots_of_complex_main p)) pis). [:- x, 1:] ^ Suc i"
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  also have "(\<Prod>(a, i)\<in>set pis. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
    by (rule prod.distinct_set_conv_list[OF yun(5)])
  also have "\<dots> = ?exp pis" using pis yun(2,6)
  proof (induct pis)
    case (Cons pi pis)
    obtain p i where pi: "pi = (p,i)" by force
    let ?rts = "roots_of_complex_main p"
    note Cons = Cons[unfolded pi]
    have IH: "(\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i) = (?exp pis)"
      by (rule Cons(1)[OF Cons(2-4)], auto)
    from Cons(2-4)[of p i] have deg: "degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
      and p: "square_free p" "degree p \<noteq> 0" "p \<noteq> 0" "monic p" by auto
    have "(\<Prod>(a, i)\<leftarrow>(pi # pis). a ^ Suc i) = p ^ Suc i * (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
      unfolding pi by simp
    also have "(\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i) = ?exp pis" by (rule IH)
    finally have id: "(\<Prod>(a, i)\<leftarrow>(pi # pis). a ^ Suc i) = p ^ Suc i * ?exp pis" by simp
    have "?exp (pi # pis) = ?exp [(p,i)] * ?exp pis" unfolding pi by simp
    also have "?exp [(p,i)] = (\<Prod>(x, i)\<leftarrow> (map (\<lambda>r. (r, i)) ?rts). [:- x, 1:] ^ Suc i)" 
      by simp
    also have "\<dots> = (\<Prod> x \<leftarrow> ?rts. [:- x, 1:])^Suc i"
      unfolding prod_list_power by (rule arg_cong[of _ _ prod_list], auto)
    also have "(\<Prod> x \<leftarrow> ?rts. [:- x, 1:]) = p" 
    proof -
      from fundamental_theorem_algebra_factorized[of p, unfolded \<open>monic p\<close>]
      obtain as where as: "p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
      also have "\<dots> = (\<Prod>a\<in>set as. [:- a, 1:])"
      proof (rule sym, rule prod.distinct_set_conv_list, rule ccontr)
        assume "\<not> distinct as" 
        from not_distinct_decomp[OF this] obtain as1 as2 as3 a where
          a: "as = as1 @ [a] @ as2 @ [a] @ as3" by blast
        define q where "q = (\<Prod>a\<leftarrow>as1 @ as2 @ as3. [:- a, 1:])"
        have "p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by fact
        also have "\<dots> = (\<Prod>a\<leftarrow>([a] @ [a]). [:- a, 1:]) * q"
          unfolding q_def a map_append prod_list.append by (simp only: ac_simps)
        also have "\<dots> = [:-a,1:] * [:-a,1:] * q" by simp
        finally have "p = ([:-a,1:] * [:-a,1:]) * q" by simp
        hence "[:-a,1:] * [:-a,1:] dvd p" unfolding dvd_def ..
        with \<open>square_free p\<close>[unfolded square_free_def, THEN conjunct2, rule_format, of "[:-a,1:]"] 
        show False by auto
      qed
      also have "set as = {x. poly p x = 0}" unfolding as poly_prod_list 
        by (simp add: o_def, induct as, auto)
      also have "\<dots> = set ?rts"
        by (rule roots_of_complex_main(1)[symmetric], insert p deg, auto)
      also have "(\<Prod>a\<in>set ?rts. [:- a, 1:]) = (\<Prod>a\<leftarrow>?rts. [:- a, 1:])"
        by (rule prod.distinct_set_conv_list[OF roots_of_complex_main(2)], insert deg p, auto)
      finally show ?thesis by simp
    qed
    finally have id2: "?exp (pi # pis) = p ^ Suc i * ?exp pis" by simp
    show ?case unfolding id id2 ..
  qed simp
  also have "?exp pis = (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)" unfolding xis ..
  finally show ?thesis unfolding p xis by simp
qed

lemma distinct_factorize_complex_main:
  assumes "factorize_complex_main p = Some fctrs"
  shows   "distinct (map fst (snd fctrs))"
proof -
  from assms have solvable: "\<forall>x\<in>set (snd (yun_factorization gcd p)). degree (fst x) \<le> 2 \<or> 
                                 (\<forall>x\<in>set (coeffs (fst x)). x \<in> \<rat>)"
    by (auto simp add: factorize_complex_main_def case_prod_unfold 
                       Let_def map_concat o_def split: if_splits)
  have sqf: "square_free_factorization p 
               (fst (yun_factorization gcd p), snd (yun_factorization gcd p))"
    by (rule yun_factorization) simp
    
  have "map fst (snd fctrs) = 
        concat (map (\<lambda>x. (roots_of_complex_main (fst x))) (snd (yun_factorization gcd p)))" 
    using assms by (auto simp add: factorize_complex_main_def case_prod_unfold 
                           Let_def map_concat o_def split: if_splits)
  also have "distinct \<dots>"
  proof (rule distinct_concat, goal_cases)
    case 1
    show ?case
    proof (subst distinct_map, safe)
      from square_free_factorizationD(5)[OF sqf]
      show "distinct (snd (yun_factorization gcd p))" .
      show "inj_on (\<lambda>x. (roots_of_complex_main (fst x))) (set (snd (yun_factorization gcd p)))"
      proof (rule inj_onI, clarify, goal_cases)
        case (1 a1 b1 a2 b2)
        {
          assume neq: "(a1, b1) \<noteq> (a2, b2)"
          from 1(1,2)[THEN square_free_factorizationD(2)[OF sqf]] 
            have "degree a1 \<noteq> 0" "degree a2 \<noteq> 0" by blast+
          hence [simp]: "a1 \<noteq> 0" "a2 \<noteq> 0" by auto
          from square_free_factorizationD(3)[OF sqf 1(1,2) neq]
            have "coprime a1 a2" by simp
          from solvable 1(1) have "{z. poly a1 z = 0} = set (roots_of_complex_main a1)"
            by (intro roots_of_complex_main(1) [symmetric]) auto
          also have "set (roots_of_complex_main a1) = set (roots_of_complex_main a2)"
            using 1(3) by (subst (1 2) set_remdups [symmetric]) (simp only: fst_conv)
          also from solvable 1(2) have "\<dots> = {z. poly a2 z = 0}"
            by (intro roots_of_complex_main) auto
          finally have "{z. poly a1 z = 0} = {z. poly a2 z = 0}" .
          with coprime_imp_no_common_roots \<open>coprime a1 a2\<close>
            have "{z. poly a1 z = 0} = {}" by auto
          with fundamental_theorem_of_algebra constant_degree
            have "degree a1 = 0" by auto
          with \<open>degree a1 \<noteq> 0\<close> have False by contradiction
        }
        thus ?case by blast
      qed
    qed  
  next
    case (2 ys)
    then obtain f b where fb: "(f, b) \<in> set (snd (yun_factorization gcd p))" 
      and ys: "ys = roots_of_complex_main f" by auto
    from square_free_factorizationD(2)[OF sqf fb] have 0: "f \<noteq> 0" by auto
    from solvable[rule_format, OF fb] have f: "degree f \<le> 2 \<or> (set (coeffs f) \<subseteq> \<rat>)" by auto
    show ?case unfolding ys 
      by (rule roots_of_complex_main[OF 0 f])
  next
    case (3 ys zs)
    then obtain a1 b1 a2 b2 where ab:
      "(a1, b1) \<in> set (snd (yun_factorization gcd p))"
      "(a2, b2) \<in> set (snd (yun_factorization gcd p))"
      "ys = roots_of_complex_main a1" "zs = roots_of_complex_main a2"
      by auto
    with 3 have neq: "(a1,b1) \<noteq> (a2,b2)" by auto
    from ab(1,2)[THEN square_free_factorizationD(2)[OF sqf]] 
      have [simp]: "a1 \<noteq> 0" "a2 \<noteq> 0" by auto
    
    from square_free_factorizationD(3)[OF sqf ab(1,2) neq] have "coprime a1 a2" by simp
    have "set ys = {z. poly a1 z = 0}" "set zs = {z. poly a2 z = 0}"
      by (insert solvable ab(1,2), subst ab,
          rule roots_of_complex_main; (auto) [])+
    with coprime_imp_no_common_roots \<open>coprime a1 a2\<close> show ?case by auto
  qed 
  
  finally show ?thesis .
qed

lemma factorize_complex_poly: assumes fp: "factorize_complex_poly p = Some (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
proof -
  from fp[unfolded factorize_complex_poly_def]
  obtain pis where fp: "factorize_complex_main p = Some (c,pis)"
    and qis: "qis = map (\<lambda>(r, i). ([:- r, 1:], Suc i)) pis"
    by auto
  from factorize_complex_main[OF fp] have p: "p = smult c (\<Prod>(x, i)\<leftarrow>pis. [:- x, 1:] ^ Suc i)" .
  show "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" unfolding p qis
    by (rule arg_cong[of _ _ "\<lambda> p. smult c (prod_list p)"], auto)
  show "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
    using linear_irreducible_field[of q] unfolding qis by auto
qed
  
end
