(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Record Based Version\<close>

text \<open>We provide an implementation for polynomials which may be parametrized
  by the ring- or field-operations. These don't have to be type-based!\<close>

subsubsection \<open>Definitions\<close>

theory Polynomial_Record_Based
imports 
  Arithmetic_Record_Based
  Karatsuba_Multiplication
begin

context
  fixes ops :: "'i arith_ops_record" (structure)
begin
private abbreviation (input) zero where "zero \<equiv> arith_ops_record.zero ops"
private abbreviation (input) one where "one \<equiv> arith_ops_record.one ops"
private abbreviation (input) plus where "plus \<equiv> arith_ops_record.plus ops"
private abbreviation (input) times where "times \<equiv> arith_ops_record.times ops"
private abbreviation (input) minus where "minus \<equiv> arith_ops_record.minus ops"
private abbreviation (input) uminus where "uminus \<equiv> arith_ops_record.uminus ops"
private abbreviation (input) divide where "divide \<equiv> arith_ops_record.divide ops"
private abbreviation (input) inverse where "inverse \<equiv> arith_ops_record.inverse ops"
private abbreviation (input) modulo where "modulo \<equiv> arith_ops_record.modulo ops"
private abbreviation (input) normalize where "normalize \<equiv> arith_ops_record.normalize ops"
private abbreviation (input) unit_factor where "unit_factor \<equiv> arith_ops_record.unit_factor ops"
private abbreviation (input) DP where "DP \<equiv> arith_ops_record.DP ops"

definition is_poly :: "'i list \<Rightarrow> bool" where
  "is_poly xs \<longleftrightarrow> list_all DP xs \<and> no_trailing (HOL.eq zero) xs"
                                        
definition cCons_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" 
where
  "cCons_i x xs = (if xs = [] \<and> x = zero then [] else x # xs)"

fun plus_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "plus_poly_i (x # xs) (y # ys) = cCons_i (plus x y) (plus_poly_i xs ys)"
| "plus_poly_i xs [] = xs"
| "plus_poly_i [] ys = ys"

definition uminus_poly_i :: "'i list \<Rightarrow> 'i list" where
  [code_unfold]: "uminus_poly_i = map uminus"

fun minus_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "minus_poly_i (x # xs) (y # ys) = cCons_i (minus x y) (minus_poly_i xs ys)"
| "minus_poly_i xs [] = xs"
| "minus_poly_i [] ys = uminus_poly_i ys"


abbreviation (input) zero_poly_i :: "'i list" where
  "zero_poly_i \<equiv> []"

definition one_poly_i :: "'i list" where
  [code_unfold]: "one_poly_i = [one]"

definition smult_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "smult_i a pp = (if a = zero then [] else strip_while ((=) zero) (map (times a) pp))"

definition sdiv_i :: "'i list \<Rightarrow> 'i \<Rightarrow> 'i list" where
  "sdiv_i pp a = (strip_while ((=) zero) (map (\<lambda> c. divide c a) pp))"

definition poly_of_list_i :: "'i list \<Rightarrow> 'i list" where
  "poly_of_list_i = strip_while ((=) zero)"

fun coeffs_minus_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "coeffs_minus_i (x # xs) (y # ys) = (minus x y # coeffs_minus_i xs ys)" 
| "coeffs_minus_i xs [] = xs" 
| "coeffs_minus_i [] ys = map uminus ys" 
  
definition monom_mult_i :: "nat \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "monom_mult_i n xs = (if xs = [] then xs else replicate n zero @ xs)" 

fun karatsuba_main_i :: "'i list \<Rightarrow> nat \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> 'i list" where
  "karatsuba_main_i f n g m = (if n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound then 
   let ff = poly_of_list_i f in foldr (\<lambda>a p. plus_poly_i (smult_i a ff) (cCons_i zero p)) g zero_poly_i
   else let n2 = n div 2 in 
   if m > n2 then (case split_at n2 f of 
   (f0,f1) \<Rightarrow> case split_at n2 g of
   (g0,g1) \<Rightarrow> let 
      p1 = karatsuba_main_i f1 (n - n2) g1 (m - n2);
      p2 = karatsuba_main_i (coeffs_minus_i f1 f0) n2 (coeffs_minus_i g1 g0) n2;
      p3 = karatsuba_main_i f0 n2 g0 n2 
      in plus_poly_i (monom_mult_i (n2 + n2) p1) 
        (plus_poly_i (monom_mult_i n2 (plus_poly_i (minus_poly_i p1 p2) p3)) p3))
    else case split_at n2 f of
    (f0,f1) \<Rightarrow> let 
       p1 = karatsuba_main_i f1 (n - n2) g m; 
       p2 = karatsuba_main_i f0 n2 g m
     in plus_poly_i (monom_mult_i n2 p1) p2)" 
  
definition times_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "times_poly_i f g \<equiv> (let n = length f; m = length g
    in (if n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound then if n \<le> m then 
      foldr (\<lambda>a p. plus_poly_i (smult_i a g) (cCons_i zero p)) f zero_poly_i else 
      foldr (\<lambda>a p. plus_poly_i (smult_i a f) (cCons_i zero p)) g zero_poly_i else
      if n \<le> m then karatsuba_main_i g m f n else karatsuba_main_i f n g m))"

definition coeff_i :: "'i list \<Rightarrow> nat \<Rightarrow> 'i" where
  "coeff_i = nth_default zero"

definition degree_i :: "'i list \<Rightarrow> nat" where
  "degree_i pp \<equiv> length pp - 1"

definition lead_coeff_i :: "'i list \<Rightarrow> 'i" where
  "lead_coeff_i pp = (case pp of [] \<Rightarrow> zero | _ \<Rightarrow> last pp)"

definition monic_i :: "'i list \<Rightarrow> bool" where
  "monic_i pp = (lead_coeff_i pp = one)" 

fun minus_poly_rev_list_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "minus_poly_rev_list_i (x # xs) (y # ys) = (minus x y) # (minus_poly_rev_list_i xs ys)"
| "minus_poly_rev_list_i xs [] = xs"
| "minus_poly_rev_list_i [] (y # ys) = []"

fun divmod_poly_one_main_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list 
  \<Rightarrow> nat \<Rightarrow> 'i list \<times> 'i list" where
  "divmod_poly_one_main_i q r d (Suc n) = (let
     a = hd r;
     qqq = cCons_i a q;
     rr = tl (if a = zero then r else minus_poly_rev_list_i r (map (times a) d))
     in divmod_poly_one_main_i qqq rr d n)"
| "divmod_poly_one_main_i q r d 0 = (q,r)"

fun mod_poly_one_main_i :: "'i list \<Rightarrow> 'i list 
  \<Rightarrow> nat \<Rightarrow> 'i list" where
  "mod_poly_one_main_i r d (Suc n) = (let
     a = hd r;
     rr = tl (if a = zero then r else minus_poly_rev_list_i r (map (times a) d))
     in mod_poly_one_main_i rr d n)"
| "mod_poly_one_main_i r d 0 = r"

definition pdivmod_monic_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<times> 'i list" where
  "pdivmod_monic_i cf cg \<equiv> case 
     divmod_poly_one_main_i [] (rev cf) (rev cg) (1 + length cf - length cg)
     of (q,r) \<Rightarrow> (poly_of_list_i q, poly_of_list_i (rev r))"

definition dupe_monic_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<times> 'i list" where
  "dupe_monic_i D H S T U = (case pdivmod_monic_i (times_poly_i T U) D of (Q,R) \<Rightarrow>
     (plus_poly_i (times_poly_i S U) (times_poly_i H Q), R))"

definition of_int_poly_i :: "int poly \<Rightarrow> 'i list" where
  "of_int_poly_i f = map (arith_ops_record.of_int ops) (coeffs f)" 

definition to_int_poly_i :: "'i list \<Rightarrow> int poly" where
  "to_int_poly_i f = poly_of_list (map (arith_ops_record.to_int ops) f)" 

definition dupe_monic_i_int :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "dupe_monic_i_int D H S T = (let 
      d = of_int_poly_i D;
      h = of_int_poly_i H;
      s = of_int_poly_i S;
      t = of_int_poly_i T 
    in (\<lambda> U. case dupe_monic_i d h s t (of_int_poly_i U) of
       (D',H') \<Rightarrow> (to_int_poly_i D', to_int_poly_i H')))"

definition div_field_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where 
  "div_field_poly_i cf cg = (
      if cg = [] then zero_poly_i
        else let ilc = inverse (last cg); ch = map (times ilc) cg;
                 q = fst (divmod_poly_one_main_i [] (rev cf) (rev ch) (1 + length cf - length cg))
             in poly_of_list_i ((map (times ilc) q)))"

definition mod_field_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where 
  "mod_field_poly_i cf cg = (
      if cg = [] then cf
        else let ilc = inverse (last cg); ch = map (times ilc) cg;
                 r = mod_poly_one_main_i (rev cf) (rev ch) (1 + length cf - length cg)
             in poly_of_list_i (rev r))"

definition normalize_poly_i :: "'i list \<Rightarrow> 'i list" where 
  "normalize_poly_i xs = smult_i (inverse (unit_factor (lead_coeff_i xs))) xs"

definition unit_factor_poly_i :: "'i list \<Rightarrow> 'i list" where 
  "unit_factor_poly_i xs = cCons_i (unit_factor (lead_coeff_i xs)) []"

fun pderiv_main_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "pderiv_main_i f (x # xs) = cCons_i (times f x) (pderiv_main_i (plus f one) xs)"
| "pderiv_main_i f [] = []"

definition pderiv_i :: "'i list \<Rightarrow> 'i list" where
  "pderiv_i xs = pderiv_main_i one (tl xs)"

definition dvd_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> bool" where
  "dvd_poly_i xs ys = (\<exists> zs. is_poly zs \<and> ys = times_poly_i xs zs)"

definition irreducible_i :: "'i list \<Rightarrow> bool" where
  "irreducible_i xs = (degree_i xs \<noteq> 0 \<and>
  (\<forall>q r. is_poly q \<longrightarrow> is_poly r \<longrightarrow> degree_i q < degree_i xs \<longrightarrow> degree_i r < degree_i xs 
    \<longrightarrow> xs \<noteq> times_poly_i q r))" 

definition poly_ops :: "'i list arith_ops_record" where
  "poly_ops \<equiv> Arith_Ops_Record
      zero_poly_i
      one_poly_i 
      plus_poly_i
      times_poly_i
      minus_poly_i
      uminus_poly_i
      div_field_poly_i
      (\<lambda> _. []) \<comment> \<open>not defined\<close>
      mod_field_poly_i
      normalize_poly_i
      unit_factor_poly_i
      (\<lambda> i. if i = 0 then [] else [arith_ops_record.of_int ops i])
      (\<lambda> _. 0) \<comment> \<open>not defined\<close>
      is_poly"


definition gcd_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "gcd_poly_i = arith_ops.gcd_eucl_i poly_ops"

definition euclid_ext_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> ('i list \<times> 'i list) \<times> 'i list" where
  "euclid_ext_poly_i = arith_ops.euclid_ext_i poly_ops"

definition separable_i :: "'i list \<Rightarrow> bool" where
  "separable_i xs \<equiv> gcd_poly_i xs (pderiv_i xs) = one_poly_i"

end

(* **************************************************************************** *)
subsubsection \<open>Properties\<close>

definition pdivmod_monic :: "'a::comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "pdivmod_monic f g \<equiv> let cg = coeffs g; cf = coeffs f; 
     (q, r) = divmod_poly_one_main_list [] (rev cf) (rev cg) (1 + length cf - length cg)
         in (poly_of_list q, poly_of_list (rev r))"

lemma coeffs_smult': "coeffs (smult a p) = (if a = 0 then [] else strip_while ((=) 0) (map (Groups.times a) (coeffs p)))" 
   by (simp add: coeffs_map_poly smult_conv_map_poly)

lemma coeffs_sdiv: "coeffs (sdiv_poly p a) = (strip_while ((=) 0) (map (\<lambda> x. x div a) (coeffs p)))"
  unfolding sdiv_poly_def by (rule coeffs_map_poly)

lifting_forget poly.lifting

context ring_ops
begin

definition poly_rel :: "'i list \<Rightarrow> 'a poly \<Rightarrow> bool" where
  "poly_rel x x' \<longleftrightarrow> list_all2 R x (coeffs x')"

lemma right_total_poly_rel[transfer_rule]: 
  "right_total poly_rel"
  using list.right_total_rel[of R] right_total unfolding poly_rel_def right_total_def by auto

lemma poly_rel_inj: "poly_rel x y \<Longrightarrow> poly_rel x z \<Longrightarrow> y = z" 
  using list.bi_unique_rel[OF bi_unique] unfolding poly_rel_def coeffs_eq_iff bi_unique_def by auto

lemma bi_unique_poly_rel[transfer_rule]: "bi_unique poly_rel"
  using list.bi_unique_rel[OF bi_unique] unfolding poly_rel_def bi_unique_def coeffs_eq_iff by auto

lemma Domainp_is_poly [transfer_domain_rule]: 
  "Domainp poly_rel = is_poly ops"
unfolding poly_rel_def [abs_def] is_poly_def [abs_def]
proof (intro ext iffI, unfold Domainp_iff)
  note DPR = fun_cong [OF list.Domainp_rel [of R, unfolded DPR],
    unfolded Domainp_iff]
  let ?no_trailing = "no_trailing (HOL.eq zero)"
  fix xs
  have no_trailing: "no_trailing (HOL.eq 0) xs' \<longleftrightarrow> ?no_trailing xs"
    if "list_all2 R xs xs'" for xs'
  proof (cases xs rule: rev_cases)
    case Nil
    with that show ?thesis
      by simp
  next
    case (snoc ys y)
    with that have "xs' \<noteq> []"
      by auto
    then obtain ys' y' where "xs' = ys' @ [y']"
      by (cases xs' rule: rev_cases) simp_all
    with that snoc show ?thesis
      by simp (meson bi_unique bi_unique_def zero)
  qed
  let ?DPR = "arith_ops_record.DP ops"
  {
    assume "\<exists>x'. list_all2 R xs (coeffs x')"
    then obtain xs' where *: "list_all2 R xs (coeffs xs')" by auto
    with DPR [of xs] have "list_all ?DPR xs" by auto
    then show "list_all ?DPR xs \<and> ?no_trailing xs"
      using no_trailing [OF *] by simp
  }
  {
    assume "list_all ?DPR xs \<and> ?no_trailing xs"
    with DPR [of xs] obtain xs' where *: "list_all2 R xs xs'" and "?no_trailing xs" 
      by auto
    from no_trailing [OF *] this(2) have "no_trailing (HOL.eq 0) xs'"
      by simp
    hence "coeffs (poly_of_list xs') = xs'" unfolding poly_of_list_impl by auto
    with * show "\<exists>x'. list_all2 R xs (coeffs x')" by metis
  }
qed

(* zero *)
lemma poly_rel_zero[transfer_rule]: "poly_rel zero_poly_i 0"
  unfolding poly_rel_def by auto

(* one *)
lemma poly_rel_one[transfer_rule]: "poly_rel (one_poly_i ops) 1"
  unfolding poly_rel_def one_poly_i_def by (simp add: one)

(* cCons *)
lemma poly_rel_cCons[transfer_rule]: "(R ===> list_all2 R ===> list_all2 R) (cCons_i ops) cCons"
  unfolding cCons_i_def[abs_def] cCons_def[abs_def] 
  by transfer_prover

(* pCons *)
lemma poly_rel_pCons[transfer_rule]: "(R ===> poly_rel ===> poly_rel) (cCons_i ops) pCons"
  unfolding rel_fun_def poly_rel_def coeffs_pCons_eq_cCons cCons_def[symmetric]
  using poly_rel_cCons[unfolded rel_fun_def] by auto

(* equality *)
lemma poly_rel_eq[transfer_rule]: "(poly_rel ===> poly_rel ===> (=)) (=) (=)"
  unfolding poly_rel_def[abs_def] coeffs_eq_iff[abs_def] rel_fun_def
  by (metis bi_unique bi_uniqueDl bi_uniqueDr list.bi_unique_rel)

(* addition *)
lemma poly_rel_plus[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (plus_poly_i ops) (+)"
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume "poly_rel x1 x2" and "poly_rel y1 y2"
  thus "poly_rel (plus_poly_i ops x1 y1) (x2 + y2)"
    unfolding poly_rel_def coeffs_eq_iff coeffs_plus_eq_plus_coeffs
  proof (induct x1 y1 arbitrary: x2 y2 rule: plus_poly_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "coeffs X2 = x2 # coeffs xs2" 
      by (cases X2, auto simp: cCons_def split: if_splits)
    from 1(3) obtain y2 ys2 where Y2: "coeffs Y2 = y2 # coeffs ys2" 
      by (cases Y2, auto simp: cCons_def split: if_splits)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 (coeffs xs2)" "list_all2 R ys1 (coeffs ys2)" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by simp transfer_prover
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases "coeffs xs2", auto)
  next
    case (3 xs2 y1 ys1 Y2)
    thus ?case by (cases Y2, auto simp: cCons_def)
  qed
qed

(* unary minus *)
lemma poly_rel_uminus[transfer_rule]: "(poly_rel ===> poly_rel) (uminus_poly_i ops) Groups.uminus"
proof (intro rel_funI)
  fix x y
  assume "poly_rel x y" 
  hence [transfer_rule]: "list_all2 R x (coeffs y)" unfolding poly_rel_def .
  show "poly_rel (uminus_poly_i ops x) (-y)"
    unfolding poly_rel_def coeffs_uminus uminus_poly_i_def by transfer_prover
qed

(* subtraction *)
lemma poly_rel_minus[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (minus_poly_i ops) (-)"
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume "poly_rel x1 x2" and "poly_rel y1 y2"
  thus "poly_rel (minus_poly_i ops x1 y1) (x2 - y2)"
    unfolding diff_conv_add_uminus
    unfolding poly_rel_def coeffs_eq_iff coeffs_plus_eq_plus_coeffs coeffs_uminus
  proof (induct x1 y1 arbitrary: x2 y2 rule: minus_poly_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "coeffs X2 = x2 # coeffs xs2" 
      by (cases X2, auto simp: cCons_def split: if_splits)
    from 1(3) obtain y2 ys2 where Y2: "coeffs Y2 = y2 # coeffs ys2" 
      by (cases Y2, auto simp: cCons_def split: if_splits)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 (coeffs xs2)" "list_all2 R ys1 (coeffs ys2)" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by simp transfer_prover
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases "coeffs xs2", auto)
  next
    case (3 xs2 y1 ys1 Y2)
    from 3(1) have id0: "coeffs ys1 = coeffs 0" by (cases ys1, auto)
    have id1: "minus_poly_i ops [] (xs2 # y1) = uminus_poly_i ops (xs2 # y1)" by simp
    from 3(2) have [transfer_rule]: "poly_rel (xs2 # y1) Y2" unfolding poly_rel_def by simp
    show ?case unfolding id0 id1 coeffs_uminus[symmetric] coeffs_plus_eq_plus_coeffs[symmetric]
      poly_rel_def[symmetric] by simp transfer_prover
  qed
qed

(* smult *)
lemma poly_rel_smult[transfer_rule]: "(R ===> poly_rel ===> poly_rel) (smult_i ops) smult"
  unfolding rel_fun_def poly_rel_def coeffs_smult' smult_i_def
proof (intro allI impI, goal_cases)
  case (1 x y xs ys)
  note [transfer_rule] = 1
  show ?case by transfer_prover
qed

(* coeffs *)
lemma poly_rel_coeffs[transfer_rule]: "(poly_rel ===> list_all2 R) (\<lambda> x. x) coeffs"
  unfolding rel_fun_def poly_rel_def by auto

(* poly_of_list *)  
lemma poly_rel_poly_of_list[transfer_rule]: "(list_all2 R ===> poly_rel) (poly_of_list_i ops) poly_of_list"
  unfolding rel_fun_def poly_of_list_i_def poly_rel_def poly_of_list_impl
proof (intro allI impI, goal_cases)
  case (1 x y)
  note [transfer_rule] = this
  show ?case by transfer_prover
qed

lemma poly_rel_monom_mult[transfer_rule]: 
  "((=) ===> poly_rel ===> poly_rel) (monom_mult_i ops) monom_mult" 
  unfolding rel_fun_def monom_mult_i_def poly_rel_def monom_mult_code Let_def
proof (auto, goal_cases)
  case (1 x xs y)
  show ?case by (induct x, auto simp: 1(3) zero)
qed

declare karatsuba_main_i.simps[simp del]

lemma list_rel_coeffs_minus_i: assumes "list_all2 R x1 x2" "list_all2 R y1 y2" 
  shows "list_all2 R (coeffs_minus_i ops x1 y1) (coeffs_minus x2 y2)" 
proof -
  note simps = coeffs_minus_i.simps coeffs_minus.simps
  show ?thesis using assms
  proof (induct x1 y1 arbitrary: x2 y2 rule: coeffs_minus_i.induct)
    case (1 x xs y ys)
    from 1(2-) obtain Y Ys where y2: "y2 = Y # Ys" unfolding list_all2_conv_all_nth by (cases y2, auto)
    with 1(2-) have y: "R y Y" "list_all2 R ys Ys" by auto
    from 1(2-) obtain X Xs where x2: "x2 = X # Xs" unfolding list_all2_conv_all_nth by (cases x2, auto)
    with 1(2-) have x: "R x X" "list_all2 R xs Xs" by auto
    from 1(1)[OF x(2) y(2)] x(1) y(1)
    show ?case unfolding x2 y2 simps using minus[unfolded rel_fun_def] by auto
  next
    case (3 y ys)
    from 3 have x2: "x2 = []" by auto
    from 3 obtain Y Ys where y2: "y2 = Y # Ys" unfolding list_all2_conv_all_nth by (cases y2, auto)
    obtain y1 where y1: "y # ys = y1" by auto
    show ?case unfolding y2 simps x2 unfolding y2[symmetric] list_all2_map2 list_all2_map1
      using 3(2) unfolding y1 using uminus[unfolded rel_fun_def]
      unfolding list_all2_conv_all_nth by auto
  qed auto
qed  

(* multiplication *)
lemma poly_rel_karatsuba_main: "list_all2 R x1 x2 \<Longrightarrow> list_all2 R y1 y2 \<Longrightarrow>
  poly_rel (karatsuba_main_i ops x1 n y1 m) (karatsuba_main x2 n y2 m)"
proof (induct n arbitrary: x1 y1 x2 y2 m rule: less_induct)
  case (less n f g F G m)
  note simp[simp] = karatsuba_main.simps[of F n G m] karatsuba_main_i.simps[of ops f n g m] 
  note IH = less(1)
  note rel[transfer_rule] = less(2-3)
  show ?case (is "poly_rel ?lhs ?rhs")
  proof (cases "(n \<le> karatsuba_lower_bound \<or> m \<le> karatsuba_lower_bound) = False")
    case False
    from False 
    have lhs: "?lhs = foldr (\<lambda>a p. plus_poly_i ops (smult_i ops a (poly_of_list_i ops f))
         (cCons_i ops zero p)) g []" by simp
    from False have rhs: "?rhs = foldr (\<lambda>a p. smult a (poly_of_list F) + pCons 0 p) G 0" by simp
    show ?thesis unfolding lhs rhs by transfer_prover
  next
    case True note * = this
    let ?n2 = "n div 2" 
    have "?n2 < n" "n - ?n2 < n" using True unfolding karatsuba_lower_bound_def by auto
    note IH = IH[OF this(1)] IH[OF this(2)]
    obtain f1 f0 where f: "split_at ?n2 f = (f0,f1)" by force
    obtain g1 g0 where g: "split_at ?n2 g = (g0,g1)" by force
    obtain F1 F0 where F: "split_at ?n2 F = (F0,F1)" by force
    obtain G1 G0 where G: "split_at ?n2 G = (G0,G1)" by force
    from rel f F have relf[transfer_rule]: "list_all2 R f0 F0" "list_all2 R f1 F1" 
      unfolding split_at_def by auto
    from rel g G have relg[transfer_rule]: "list_all2 R g0 G0" "list_all2 R g1 G1" 
      unfolding split_at_def by auto
    show ?thesis
    proof (cases "?n2 < m")
      case True
      obtain p1 P1 where p1: "p1 = karatsuba_main_i ops f1 (n - n div 2) g1 (m - n div 2)" 
          "P1 = karatsuba_main F1 (n - n div 2) G1 (m - n div 2)" by auto
      obtain p2 P2 where p2: "p2 = karatsuba_main_i ops (coeffs_minus_i ops f1 f0) (n div 2)
                          (coeffs_minus_i ops g1 g0) (n div 2)" 
          "P2 = karatsuba_main (coeffs_minus F1 F0) (n div 2)
                          (coeffs_minus G1 G0) (n div 2)" by auto 
      obtain p3 P3 where p3: "p3 = karatsuba_main_i ops f0 (n div 2) g0 (n div 2)"
          "P3 = karatsuba_main F0 (n div 2) G0 (n div 2)" by auto
      from * True have lhs: "?lhs = plus_poly_i ops (monom_mult_i ops (n div 2 + n div 2) p1)
                (plus_poly_i ops
                  (monom_mult_i ops (n div 2)
                    (plus_poly_i ops (minus_poly_i ops p1 p2) p3)) p3)" 
        unfolding simp Let_def f g split p1 p2 p3 by auto
      have [transfer_rule]: "poly_rel p1 P1" using IH(2)[OF relf(2) relg(2)] unfolding p1 .
      have [transfer_rule]: "poly_rel p3 P3" using IH(1)[OF relf(1) relg(1)] unfolding p3 .
      have [transfer_rule]: "poly_rel p2 P2" unfolding p2 
        by (rule IH(1)[OF list_rel_coeffs_minus_i list_rel_coeffs_minus_i], insert relf relg)
      from True * have rhs: "?rhs = monom_mult (n div 2 + n div 2) P1 +
               (monom_mult (n div 2) (P1 - P2 + P3) + P3)" 
        unfolding simp Let_def F G split p1 p2 p3 by auto
      show ?thesis unfolding lhs rhs by transfer_prover 
    next
      case False
      obtain p1 P1 where p1: "p1 = karatsuba_main_i ops f1 (n - n div 2) g m" 
          "P1 = karatsuba_main F1 (n - n div 2) G m" by auto 
      obtain p2 P2 where p2: "p2 = karatsuba_main_i ops f0 (n div 2) g m" 
          "P2 = karatsuba_main F0 (n div 2) G m" by auto
      from * False have lhs: "?lhs = plus_poly_i ops (monom_mult_i ops (n div 2) p1) p2" 
        unfolding simp Let_def f split p1 p2 by auto
      from * False have rhs: "?rhs = monom_mult (n div 2) P1 + P2" 
        unfolding simp Let_def F split p1 p2 by auto
      have [transfer_rule]: "poly_rel p1 P1" using IH(2)[OF relf(2) rel(2)] unfolding p1 .
      have [transfer_rule]: "poly_rel p2 P2" using IH(1)[OF relf(1) rel(2)] unfolding p2 .
      show ?thesis unfolding lhs rhs by transfer_prover 
    qed
  qed
qed
  

lemma poly_rel_times[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (times_poly_i ops) ((*))"  
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume x12[transfer_rule]: "poly_rel x1 x2" and y12 [transfer_rule]: "poly_rel y1 y2"
  hence X12[transfer_rule]: "list_all2 R x1 (coeffs x2)" and Y12[transfer_rule]: "list_all2 R y1 (coeffs y2)" 
    unfolding poly_rel_def by auto
  hence len: "length (coeffs x2) = length x1" "length (coeffs y2) = length y1" 
    unfolding list_all2_conv_all_nth by auto
  let ?cond1 = "length x1 \<le> karatsuba_lower_bound \<or> length y1 \<le> karatsuba_lower_bound" 
  let ?cond2 = "length x1 \<le> length y1" 
  note d = karatsuba_mult_poly[symmetric] karatsuba_mult_poly_def Let_def
      times_poly_i_def len if_True if_False
  consider (TT) "?cond1 = True" "?cond2 = True" | (TF) "?cond1 = True" "?cond2 = False" 
      | (FT) "?cond1 = False" "?cond2 = True" | (FF) "?cond1 = False" "?cond2 = False" by auto
  thus "poly_rel (times_poly_i ops x1 y1) (x2 * y2)"
  proof (cases)
    case TT
    show ?thesis unfolding d TT 
      unfolding poly_rel_def coeffs_eq_iff times_poly_def times_poly_i_def fold_coeffs_def
      by transfer_prover
  next
    case TF
    show ?thesis unfolding d TF
      unfolding poly_rel_def coeffs_eq_iff times_poly_def times_poly_i_def fold_coeffs_def
      by transfer_prover
  next
    case FT
    show ?thesis unfolding d FT
      by (rule poly_rel_karatsuba_main[OF Y12 X12])
  next
    case FF
    show ?thesis unfolding d FF
      by (rule poly_rel_karatsuba_main[OF X12 Y12])
  qed
qed

(* coeff *)  
lemma poly_rel_coeff[transfer_rule]: "(poly_rel ===> (=) ===> R) (coeff_i ops) coeff"
  unfolding poly_rel_def rel_fun_def coeff_i_def nth_default_coeffs_eq[symmetric]
proof (intro allI impI, clarify)
  fix x y n
  assume [transfer_rule]: "list_all2 R x (coeffs y)"
  show "R (nth_default zero x n) (nth_default 0 (coeffs y) n)" by transfer_prover
qed

(* degree *)
lemma poly_rel_degree[transfer_rule]: "(poly_rel ===> (=)) degree_i degree"
  unfolding poly_rel_def rel_fun_def degree_i_def degree_eq_length_coeffs 
  by (simp add: list_all2_lengthD)

(* lead_coeff *)
lemma lead_coeff_i_def': "lead_coeff_i ops x = (coeff_i ops) x (degree_i x)"
  unfolding lead_coeff_i_def degree_i_def coeff_i_def
proof (cases x, auto, goal_cases)
  case (1 a xs)
  hence id: "last xs = last (a # xs)" by auto
  show ?case unfolding id by (subst last_conv_nth_default, auto)
qed

lemma poly_rel_lead_coeff[transfer_rule]: "(poly_rel ===> R) (lead_coeff_i ops) lead_coeff"
  unfolding lead_coeff_i_def' [abs_def] by transfer_prover

(* minus_poly_rev_list *)
lemma poly_rel_minus_poly_rev_list[transfer_rule]: 
  "(list_all2 R ===> list_all2 R ===> list_all2 R) (minus_poly_rev_list_i ops) minus_poly_rev_list"
proof (intro rel_funI, goal_cases)
  case (1 x1 x2 y1 y2)
  thus ?case
  proof (induct x1 y1 arbitrary: x2 y2 rule: minus_poly_rev_list_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "X2 = x2 # xs2" by (cases X2, auto)
    from 1(3) obtain y2 ys2 where Y2: "Y2 = y2 # ys2" by (cases Y2, auto)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 xs2" "list_all2 R ys1 ys2" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by (simp, intro conjI, transfer_prover+)
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases xs2, auto)
  next
    case (3 xs2 y1 ys1 Y2)
    thus ?case by (cases Y2, auto)
  qed
qed

(* division *)
lemma divmod_poly_one_main_i: assumes len: "n \<le> length Y" and rel: "list_all2 R x X" "list_all2 R y Y"
    "list_all2 R z Z" and n: "n = N"
 shows "rel_prod (list_all2 R) (list_all2 R) (divmod_poly_one_main_i ops x y z n)
    (divmod_poly_one_main_list X Y Z N)"
   using len rel unfolding n 
proof (induct N arbitrary: x X y Y z Z)
  case (Suc n x X y Y z Z)
  from Suc(2,4) have [transfer_rule]: "R (hd y) (hd Y)" by (cases y; cases Y, auto)  
  note [transfer_rule] = Suc(3-5)
  have id: "?case = (rel_prod (list_all2 R) (list_all2 R)
     (divmod_poly_one_main_i ops (cCons_i ops (hd y) x)
       (tl (if hd y = zero then y else minus_poly_rev_list_i ops y (map (times (hd y)) z))) z n)
     (divmod_poly_one_main_list (cCons (hd Y) X)
       (tl (if hd Y = 0 then Y else minus_poly_rev_list Y (map ((*) (hd Y)) Z))) Z n))"
     by (simp add: Let_def)
  show ?case unfolding id
  proof (rule Suc(1), goal_cases)
    case 1
    show ?case using Suc(2) by simp 
  qed (transfer_prover+)
qed simp

(* modulo *)
lemma mod_poly_one_main_i: assumes len: "n \<le> length X" and rel: "list_all2 R x X" "list_all2 R y Y"
    and n: "n = N"
 shows "list_all2 R (mod_poly_one_main_i ops x y n)
    (mod_poly_one_main_list X Y N)"
   using len rel unfolding n 
proof (induct N arbitrary: x X y Y)
  case (Suc n y Y z Z)
  from Suc(2,3) have [transfer_rule]: "R (hd y) (hd Y)" by (cases y; cases Y, auto)  
  note [transfer_rule] = Suc(3-4)
  have id: "?case = (list_all2 R
     (mod_poly_one_main_i ops
       (tl (if hd y = zero then y else minus_poly_rev_list_i ops y (map (times (hd y)) z))) z n)
     (mod_poly_one_main_list 
       (tl (if hd Y = 0 then Y else minus_poly_rev_list Y (map ((*) (hd Y)) Z))) Z n))"
     by (simp add: Let_def)
  show ?case unfolding id
  proof (rule Suc(1), goal_cases)
    case 1
    show ?case using Suc(2) by simp 
  qed (transfer_prover+)
qed simp

lemma poly_rel_dvd[transfer_rule]: "(poly_rel ===> poly_rel ===> (=)) (dvd_poly_i ops) (dvd)"
  unfolding dvd_poly_i_def[abs_def] dvd_def[abs_def] 
  by (transfer_prover_start, transfer_step+, auto)

lemma poly_rel_monic[transfer_rule]: "(poly_rel ===> (=)) (monic_i ops) monic"
  unfolding monic_i_def lead_coeff_i_def' by transfer_prover

lemma poly_rel_pdivmod_monic: assumes mon: "monic Y" 
  and x: "poly_rel x X" and y: "poly_rel y Y"
  shows "rel_prod poly_rel poly_rel (pdivmod_monic_i ops x y) (pdivmod_monic X Y)"
proof -
  note [transfer_rule] = x y
  note listall = this[unfolded poly_rel_def]
  note defs = pdivmod_monic_def pdivmod_monic_i_def Let_def
  from mon obtain k where len: "length (coeffs Y) = Suc k" unfolding poly_rel_def list_all2_iff 
      by (cases "coeffs Y", auto)
  have [transfer_rule]: 
    "rel_prod (list_all2 R) (list_all2 R)
       (divmod_poly_one_main_i ops [] (rev x) (rev y) (1 + length x - length y))
       (divmod_poly_one_main_list [] (rev (coeffs X)) (rev (coeffs Y)) (1 + length (coeffs X) - length (coeffs Y)))" 
    by (rule divmod_poly_one_main_i, insert x y listall, auto, auto simp: poly_rel_def list_all2_iff len)
  show ?thesis unfolding defs by transfer_prover
qed

lemma ring_ops_poly: "ring_ops (poly_ops ops) poly_rel"
  by (unfold_locales, auto simp: poly_ops_def  
  bi_unique_poly_rel 
  right_total_poly_rel
  poly_rel_times
  poly_rel_zero 
  poly_rel_one
  poly_rel_minus
  poly_rel_uminus
  poly_rel_plus
  poly_rel_eq
  Domainp_is_poly)
end

context idom_ops
begin

(* pderiv *)
lemma poly_rel_pderiv [transfer_rule]: "(poly_rel ===> poly_rel) (pderiv_i ops) pderiv"
proof (intro rel_funI, unfold poly_rel_def coeffs_pderiv_code pderiv_i_def pderiv_coeffs_def)
  fix xs xs'
  assume "list_all2 R xs (coeffs xs')"
  then obtain ys ys' y y' where id: "tl xs = ys" "tl (coeffs xs') = ys'" "one = y" "1 = y'" and 
    R: "list_all2 R ys ys'" "R y y'"
    by (cases xs; cases "coeffs xs'"; auto simp: one)
  show "list_all2 R (pderiv_main_i ops one (tl xs))
            (pderiv_coeffs_code 1 (tl (coeffs xs')))"
    unfolding id using R
  proof (induct ys ys' arbitrary: y y' rule: list_all2_induct)
    case (Cons x xs x' xs' y y')
    note [transfer_rule] = Cons(1,2,4)
    have "R (plus y one) (y' + 1)"  by transfer_prover
    note [transfer_rule] = Cons(3)[OF this]
    show ?case by (simp, transfer_prover)
  qed simp
qed 

lemma poly_rel_irreducible[transfer_rule]: "(poly_rel ===> (=)) (irreducible_i ops) irreducible\<^sub>d"
  unfolding irreducible_i_def[abs_def] irreducible\<^sub>d_def[abs_def] 
  by (transfer_prover_start, transfer_step+, auto)

lemma idom_ops_poly: "idom_ops (poly_ops ops) poly_rel"
  using ring_ops_poly unfolding ring_ops_def idom_ops_def by auto
end

context idom_divide_ops
begin
(* sdiv *)
lemma poly_rel_sdiv[transfer_rule]: "(poly_rel ===> R ===> poly_rel) (sdiv_i ops) sdiv_poly"
  unfolding rel_fun_def poly_rel_def coeffs_sdiv sdiv_i_def
proof (intro allI impI, goal_cases)
  case (1 x y xs ys)
  note [transfer_rule] = 1
  show ?case by transfer_prover
qed
end

context field_ops
begin
(* division *)
lemma poly_rel_div[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) 
  (div_field_poly_i ops) (div)"
proof (intro rel_funI, goal_cases)
  case (1 x X y Y)
  note [transfer_rule] = this
  note listall = this[unfolded poly_rel_def]
  note defs = div_field_poly_impl div_field_poly_impl_def div_field_poly_i_def Let_def
  show ?case 
  proof (cases "y = []")
    case True
    with 1(2) have nil: "coeffs Y = []" unfolding poly_rel_def by auto
    show ?thesis unfolding defs True nil poly_rel_def by auto
  next
    case False
    from append_butlast_last_id[OF False] obtain ys yl where y: "y = ys @ [yl]" by metis
    from False listall have "coeffs Y \<noteq> []" by auto
    from append_butlast_last_id[OF this] obtain Ys Yl where Y: "coeffs Y = Ys @ [Yl]" by metis
    from listall have [transfer_rule]: "R yl Yl" by (simp add: y Y)
    have id: "last (coeffs Y) = Yl" "last (y) = yl" 
      "\<And> t e. (if y = [] then t else e) = e"
      "\<And> t e. (if coeffs Y = [] then t else e) = e" unfolding y Y by auto
    have [transfer_rule]: "(rel_prod (list_all2 R) (list_all2 R)) 
      (divmod_poly_one_main_i ops [] (rev x) (rev (map (times (inverse yl)) y))
        (1 + length x - length y))
      (divmod_poly_one_main_list [] (rev (coeffs X))
                (rev (map ((*) (Fields.inverse Yl)) (coeffs Y)))
                (1 + length (coeffs X) - length (coeffs Y)))"
    proof (rule divmod_poly_one_main_i, goal_cases)
      case 5
      from listall show ?case by (simp add: list_all2_lengthD)
    next
      case 1
      from listall show ?case by (simp add: list_all2_lengthD Y)
    qed transfer_prover+      
    show ?thesis unfolding defs id by transfer_prover
  qed
qed

(* modulo *)
lemma poly_rel_mod[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) 
  (mod_field_poly_i ops) (mod)"
proof (intro rel_funI, goal_cases)
  case (1 x X y Y)
  note [transfer_rule] = this
  note listall = this[unfolded poly_rel_def]
  note defs = mod_poly_code mod_field_poly_i_def Let_def
  show ?case 
  proof (cases "y = []")
    case True
    with 1(2) have nil: "coeffs Y = []" unfolding poly_rel_def by auto
    show ?thesis unfolding defs True nil poly_rel_def by (simp add: listall)
  next
    case False
    from append_butlast_last_id[OF False] obtain ys yl where y: "y = ys @ [yl]" by metis
    from False listall have "coeffs Y \<noteq> []" by auto
    from append_butlast_last_id[OF this] obtain Ys Yl where Y: "coeffs Y = Ys @ [Yl]" by metis
    from listall have [transfer_rule]: "R yl Yl" by (simp add: y Y)
    have id: "last (coeffs Y) = Yl" "last (y) = yl" 
      "\<And> t e. (if y = [] then t else e) = e"
      "\<And> t e. (if coeffs Y = [] then t else e) = e" unfolding y Y by auto
    have [transfer_rule]: "list_all2 R
      (mod_poly_one_main_i ops (rev x) (rev (map (times (inverse yl)) y))
        (1 + length x - length y))
      (mod_poly_one_main_list (rev (coeffs X))
                (rev (map ((*) (Fields.inverse Yl)) (coeffs Y)))
                (1 + length (coeffs X) - length (coeffs Y)))"
    proof (rule mod_poly_one_main_i, goal_cases)
      case 4
      from listall show ?case by (simp add: list_all2_lengthD)
    next
      case 1
      from listall show ?case by (simp add: list_all2_lengthD Y)
    qed transfer_prover+      
    show ?thesis unfolding defs id by transfer_prover
  qed
qed

(* normalize *)
lemma poly_rel_normalize [transfer_rule]: "(poly_rel ===> poly_rel) 
  (normalize_poly_i ops) Rings.normalize"
  unfolding normalize_poly_old_def normalize_poly_i_def lead_coeff_i_def'
  by transfer_prover

(* unit_factor *)
lemma poly_rel_unit_factor [transfer_rule]: "(poly_rel ===> poly_rel) 
  (unit_factor_poly_i ops) Rings.unit_factor"
  unfolding unit_factor_poly_def unit_factor_poly_i_def lead_coeff_i_def'
  unfolding monom_0 by transfer_prover

lemma idom_divide_ops_poly: "idom_divide_ops (poly_ops ops) poly_rel"
proof -
  interpret poly: idom_ops "poly_ops ops" poly_rel by (rule idom_ops_poly)
  show ?thesis
    by (unfold_locales, simp add: poly_rel_div poly_ops_def)
qed

lemma euclidean_ring_ops_poly: "euclidean_ring_ops (poly_ops ops) poly_rel"
proof -
  interpret poly: idom_ops "poly_ops ops" poly_rel by (rule idom_ops_poly)
  have id: "arith_ops_record.normalize (poly_ops ops) = normalize_poly_i ops"
    "arith_ops_record.unit_factor (poly_ops ops) = unit_factor_poly_i ops"
    unfolding poly_ops_def by simp_all
  show ?thesis
    by (unfold_locales, simp add: poly_rel_mod poly_ops_def, unfold id, 
      simp add: poly_rel_normalize, insert poly_rel_div poly_rel_unit_factor, 
      auto simp: poly_ops_def)
qed

(* gcd poly *)
lemma poly_rel_gcd [transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (gcd_poly_i ops) gcd"
proof -
  interpret poly: euclidean_ring_ops "poly_ops ops" poly_rel by (rule euclidean_ring_ops_poly)
  show ?thesis using poly.gcd_eucl_i unfolding gcd_poly_i_def gcd_eucl .
qed

(* euclid_ext poly *)
lemma poly_rel_euclid_ext [transfer_rule]: "(poly_rel ===> poly_rel ===> 
  rel_prod (rel_prod poly_rel poly_rel) poly_rel) (euclid_ext_poly_i ops) euclid_ext"
proof -
  interpret poly: euclidean_ring_ops "poly_ops ops" poly_rel by (rule euclidean_ring_ops_poly)
  show ?thesis using poly.euclid_ext_i unfolding euclid_ext_poly_i_def .
qed 

end

(* ********************************************************** *)

context ring_ops
begin
notepad (* checking transfer rules *)
begin
  fix xs x ys y
  assume [transfer_rule]: "poly_rel xs x" "poly_rel ys y" 
  have "x * y = y * x" by simp
  from this[untransferred]
  have "times_poly_i ops xs ys = times_poly_i ops ys xs" .
end
end
end
