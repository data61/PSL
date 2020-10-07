(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Record Based Version\<close>
theory Finite_Field_Factorization_Record_Based
imports
  Finite_Field_Factorization 
  Matrix_Record_Based
  Poly_Mod_Finite_Field_Record_Based
  "HOL-Types_To_Sets.Types_To_Sets"
  Jordan_Normal_Form.Matrix_IArray_Impl
  Jordan_Normal_Form.Gauss_Jordan_IArray_Impl  
  Polynomial_Interpolation.Improved_Code_Equations
  Polynomial_Factorization.Missing_List
begin

hide_const(open) monom coeff

text \<open>Whereas @{thm finite_field_factorization} provides a result for a polynomials over GF(p),
  we now develop a theorem which speaks about integer polynomials modulo p.\<close>
lemma (in poly_mod_prime_type) finite_field_factorization_modulo_ring:
  assumes g: "(g :: 'a mod_ring poly) = of_int_poly f"
  and sf: "square_free_m f"
  and fact: "finite_field_factorization g = (d,gs)"
  and c: "c = to_int_mod_ring d"
  and fs: "fs = map to_int_poly gs"
  shows "unique_factorization_m f (c, mset fs)"
proof -
  have [transfer_rule]: "MP_Rel f g" unfolding g MP_Rel_def by (simp add: Mp_f_representative)
  have sg: "square_free g" by (transfer, rule sf)
  have [transfer_rule]: "M_Rel c d" unfolding M_Rel_def c by (rule M_to_int_mod_ring)
  have fs_gs[transfer_rule]: "list_all2 MP_Rel fs gs"
    unfolding fs list_all2_map1 MP_Rel_def[abs_def] Mp_to_int_poly by (simp add: list.rel_refl)
  have [transfer_rule]: "rel_mset MP_Rel (mset fs) (mset gs)"
    using fs_gs using rel_mset_def by blast
  have [transfer_rule]: "MF_Rel (c,mset fs) (d,mset gs)" unfolding MF_Rel_def by transfer_prover
  from finite_field_factorization[OF sg fact]
  have uf: "unique_factorization Irr_Mon g (d,mset gs)" by auto
  from uf[untransferred] show "unique_factorization_m f (c, mset fs)" .
qed

text \<open>We now have to implement @{const finite_field_factorization}.\<close>  
context
  fixes p :: int
  and ff_ops :: "'i arith_ops_record"  (* finite-fields *)
begin

fun power_poly_f_mod_i :: "('i list \<Rightarrow> 'i list) \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> 'i list" where
  "power_poly_f_mod_i modulus a n = (if n = 0 then modulus (one_poly_i ff_ops)
    else let (d,r) = Divides.divmod_nat n 2; 
       rec = power_poly_f_mod_i modulus (modulus (times_poly_i ff_ops a a)) d in 
    if r = 0 then rec else modulus (times_poly_i ff_ops rec a))"

declare power_poly_f_mod_i.simps[simp del]

fun power_polys_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> 'i list list" where
  "power_polys_i mul_p u curr_p (Suc i) = curr_p # 
      power_polys_i mul_p u (mod_field_poly_i ff_ops (times_poly_i ff_ops curr_p mul_p) u) i"
| "power_polys_i mul_p u curr_p 0 = []"

lemma length_power_polys_i[simp]: "length (power_polys_i x y z n) = n" 
  by (induct n arbitrary: x y z, auto)

definition berlekamp_mat_i :: "'i list \<Rightarrow> 'i mat" where
  "berlekamp_mat_i u = (let n = degree_i u; 
    ze = arith_ops_record.zero ff_ops; on = arith_ops_record.one ff_ops;
    mul_p = power_poly_f_mod_i (\<lambda> v. mod_field_poly_i ff_ops v u) 
      [ze, on] (nat p);
    xks = power_polys_i mul_p u [on] n
   in mat_of_rows_list n (map (\<lambda> cs. cs @ replicate (n - length cs) ze) xks))"

definition berlekamp_resulting_mat_i :: "'i list \<Rightarrow> 'i mat" where
"berlekamp_resulting_mat_i u = (let Q = berlekamp_mat_i u;
    n = dim_row Q;
    QI = mat n n (\<lambda> (i,j). if i = j then arith_ops_record.minus ff_ops (Q $$ (i,j)) (arith_ops_record.one ff_ops) else Q $$ (i,j))
    in (gauss_jordan_single_i ff_ops (transpose_mat QI)))"

definition berlekamp_basis_i :: "'i list \<Rightarrow> 'i list list" where
  "berlekamp_basis_i u = (map (poly_of_list_i ff_ops o list_of_vec) 
    (find_base_vectors_i ff_ops (berlekamp_resulting_mat_i u)))"

primrec berlekamp_factorization_main_i :: "'i \<Rightarrow> 'i \<Rightarrow> nat \<Rightarrow> 'i list list \<Rightarrow> 'i list list \<Rightarrow> nat \<Rightarrow> 'i list list" where
  "berlekamp_factorization_main_i ze on d divs (v # vs) n = (
    if v = [on] then berlekamp_factorization_main_i ze on d divs vs n else
    if length divs = n then divs else
    let of_int = arith_ops_record.of_int ff_ops;
        facts = filter (\<lambda> w. w \<noteq> [on]) 
          [ gcd_poly_i ff_ops u (minus_poly_i ff_ops v (if s = 0 then [] else [of_int (int s)])) . 
            u \<leftarrow> divs, s \<leftarrow> [0 ..< nat p]];
      (lin,nonlin) = List.partition (\<lambda> q. degree_i q = d) facts 
      in lin @ berlekamp_factorization_main_i ze on d nonlin vs (n - length lin))"
| "berlekamp_factorization_main_i ze on d divs [] n = divs"

definition berlekamp_monic_factorization_i :: "nat \<Rightarrow> 'i list \<Rightarrow> 'i list list" where
  "berlekamp_monic_factorization_i d f = (let
     vs = berlekamp_basis_i f
    in berlekamp_factorization_main_i (arith_ops_record.zero ff_ops) (arith_ops_record.one ff_ops) d [f] vs (length vs))"         

partial_function (tailrec) dist_degree_factorize_main_i :: 
  "'i \<Rightarrow> 'i \<Rightarrow> nat \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> (nat \<times> 'i list) list 
  \<Rightarrow> (nat \<times> 'i list) list" where
  [code]: "dist_degree_factorize_main_i ze on dv v w d res = (if v = [on] then res else if d + d > dv 
    then (dv, v) # res else let
      w = power_poly_f_mod_i (\<lambda> f. mod_field_poly_i ff_ops f v) w (nat p);
      d = Suc d;
      gd = gcd_poly_i ff_ops (minus_poly_i ff_ops w [ze,on]) v
      in if gd = [on] then dist_degree_factorize_main_i ze on dv v w d res else 
      let v' = div_field_poly_i ff_ops v gd
      in dist_degree_factorize_main_i ze on (degree_i v') v' (mod_field_poly_i ff_ops w v') d ((d,gd) # res))" 

definition distinct_degree_factorization_i
  :: "'i list \<Rightarrow> (nat \<times> 'i list) list" where
  "distinct_degree_factorization_i f = (let ze = arith_ops_record.zero ff_ops;
     on = arith_ops_record.one ff_ops in if degree_i f = 1 then [(1,f)] else 
     dist_degree_factorize_main_i ze on (degree_i f) f [ze,on] 0 [])"

definition finite_field_factorization_i :: "'i list \<Rightarrow> 'i \<times> 'i list list" where
  "finite_field_factorization_i f = (if degree_i f = 0 then (lead_coeff_i ff_ops f,[]) else let
     a = lead_coeff_i ff_ops f;
     u = smult_i ff_ops (arith_ops_record.inverse ff_ops a) f;
     gs = (if use_distinct_degree_factorization then distinct_degree_factorization_i u else [(1,u)]);
     (irr,hs) = List.partition (\<lambda> (i,f). degree_i f = i) gs
     in (a,map snd irr @ concat (map (\<lambda> (i,g). berlekamp_monic_factorization_i i g) hs)))"
end

context prime_field_gen
begin

lemma power_polys_i: assumes i: "i < n" and [transfer_rule]: "poly_rel f f'" "poly_rel g g'" 
  and h: "poly_rel h h'"
  shows "poly_rel (power_polys_i ff_ops g f h n ! i) (power_polys g' f' h' n ! i)"
  using i h
proof (induct n arbitrary: h h' i)
  case (Suc n h h' i) note * = this
  note [transfer_rule] = *(3)
  show ?case 
  proof (cases i)
    case 0
    with Suc show ?thesis by auto
  next
    case (Suc j)
    with *(2-) have "j < n" by auto
    note IH = *(1)[OF this]
    show ?thesis unfolding Suc by (simp, rule IH, transfer_prover)
  qed
qed simp

lemma power_poly_f_mod_i: assumes m: "(poly_rel ===> poly_rel) m (\<lambda> x'. x' mod m')"
  shows "poly_rel f f' \<Longrightarrow> poly_rel (power_poly_f_mod_i ff_ops m f n) (power_poly_f_mod m' f' n)"
proof -
  from m have m: "\<And> x x'. poly_rel x x' \<Longrightarrow> poly_rel (m x) (x' mod m')" 
    unfolding rel_fun_def by auto
  show "poly_rel f f' \<Longrightarrow> poly_rel (power_poly_f_mod_i ff_ops m f n) (power_poly_f_mod m' f' n)"
  proof (induct n arbitrary: f f' rule: less_induct)
    case (less n f f')
    note f[transfer_rule] = less(2)
    show ?case
    proof (cases "n = 0")
      case True
      show ?thesis 
        by (simp add: True power_poly_f_mod_i.simps power_poly_f_mod_binary, 
          rule m[OF poly_rel_one])
    next
      case False
      hence n: "(n = 0) = False" by simp
      obtain q r where div: "Divides.divmod_nat n 2 = (q,r)" by force
      from this[unfolded divmod_nat_def] n have "q < n" by auto
      note IH = less(1)[OF this]
      have rec: "poly_rel (power_poly_f_mod_i ff_ops m (m (times_poly_i ff_ops f f)) q) 
        (power_poly_f_mod m' (f' * f' mod m') q)" 
        by (rule IH, rule m, transfer_prover)
      have other: "poly_rel 
        (m (times_poly_i ff_ops (power_poly_f_mod_i ff_ops m (m (times_poly_i ff_ops f f)) q) f))
        (power_poly_f_mod m' (f' * f' mod m') q * f' mod m')" 
        by (rule m, rule poly_rel_times[unfolded rel_fun_def, rule_format, OF rec f])
      show ?thesis unfolding power_poly_f_mod_i.simps[of _ _ _ n] Let_def 
        power_poly_f_mod_binary[of _ _ n] div split n if_False using rec other by auto
    qed
  qed
qed
    
lemma berlekamp_mat_i[transfer_rule]: "(poly_rel ===> mat_rel R) 
  (berlekamp_mat_i p ff_ops) berlekamp_mat"
proof (intro rel_funI)
  fix f f' 
  let ?ze = "arith_ops_record.zero ff_ops" 
  let ?on = "arith_ops_record.one ff_ops"
  assume f[transfer_rule]: "poly_rel f f'"
  have deg: "degree_i f = degree f'" by transfer_prover
  {
    fix i j
    assume i: "i < degree f'" and j: "j < degree f'" 
    define cs where "cs = (\<lambda>cs :: 'i list. cs @ replicate (degree f' - length cs) ?ze)"
    define cs' where "cs' = (\<lambda>cs :: 'a mod_ring poly. coeffs cs @ replicate (degree f' - length (coeffs cs)) 0)"
    define poly where "poly = power_polys_i ff_ops
         (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [?ze, ?on] (nat p)) f [?on]
         (degree f')"
    define poly' where "poly' = (power_polys (power_poly_f_mod f' [:0, 1:] (nat p)) f' 1 (degree f'))"
    have *: "poly_rel (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [?ze, ?on] (nat p))
      (power_poly_f_mod f' [:0, 1:] (nat p))" 
      by (rule power_poly_f_mod_i, transfer_prover, simp add: poly_rel_def one zero)
    have [transfer_rule]: "poly_rel (poly ! i) (poly' ! i)" 
      unfolding poly_def poly'_def 
      by (rule power_polys_i[OF i f *], simp add: poly_rel_def one)
    have *: "list_all2 R (cs (poly ! i)) (cs' (poly' ! i))"
      unfolding cs_def cs'_def by transfer_prover
    from list_all2_nthD[OF *[unfolded poly_rel_def], of j] j
    have "R (cs (poly ! i) ! j) (cs' (poly' ! i) ! j)" unfolding cs_def by auto
    hence "R
            (mat_of_rows_list (degree f')
              (map (\<lambda>cs. cs @ replicate (degree f' - length cs) ?ze)
                (power_polys_i ff_ops
                  (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [?ze, ?on] (nat p)) f [?on]
                  (degree f'))) $$
             (i, j))
            (mat_of_rows_list (degree f')
              (map (\<lambda>cs. coeffs cs @ replicate (degree f' - length (coeffs cs)) 0)
                (power_polys (power_poly_f_mod f' [:0, 1:] (nat p)) f' 1 (degree f'))) $$
             (i, j))"           
        unfolding mat_of_rows_list_def length_map length_power_polys_i power_polys_works
          length_power_polys index_mat[OF i j] split
        unfolding poly_def cs_def poly'_def cs'_def using i
        by auto
  } note main = this
  show "mat_rel R (berlekamp_mat_i p ff_ops f) (berlekamp_mat f')"
    unfolding berlekamp_mat_i_def berlekamp_mat_def Let_def nat_p[symmetric] deg
    unfolding mat_rel_def
    by (intro conjI allI impI, insert main, auto)
qed

lemma berlekamp_resulting_mat_i[transfer_rule]: "(poly_rel ===> mat_rel R) 
  (berlekamp_resulting_mat_i p ff_ops) berlekamp_resulting_mat"
proof (intro rel_funI)
  fix f f'
  assume "poly_rel f f'"
  from berlekamp_mat_i[unfolded rel_fun_def, rule_format, OF this]
  have bmi: "mat_rel R (berlekamp_mat_i p ff_ops f) (berlekamp_mat f')" .
  show "mat_rel R (berlekamp_resulting_mat_i p ff_ops f) (berlekamp_resulting_mat f')"
    unfolding berlekamp_resulting_mat_def Let_def berlekamp_resulting_mat_i_def
    by (rule gauss_jordan_i[unfolded rel_fun_def, rule_format],
    insert bmi, auto simp: mat_rel_def one intro!: minus[unfolded rel_fun_def, rule_format])
qed

lemma berlekamp_basis_i[transfer_rule]: "(poly_rel ===> list_all2 poly_rel) 
  (berlekamp_basis_i p ff_ops) berlekamp_basis"
  unfolding berlekamp_basis_i_def[abs_def] berlekamp_basis_code[abs_def] o_def
  by transfer_prover

lemma berlekamp_factorization_main_i[transfer_rule]: 
  "((=) ===> list_all2 poly_rel ===> list_all2 poly_rel ===> (=) ===> list_all2 poly_rel) 
     (berlekamp_factorization_main_i p ff_ops (arith_ops_record.zero ff_ops) 
       (arith_ops_record.one ff_ops)) 
     berlekamp_factorization_main" 
proof (intro rel_funI, clarify, goal_cases)
  case (1 _ d xs xs' ys ys' _ n)
  let ?ze = "arith_ops_record.zero ff_ops" 
  let ?on = "arith_ops_record.one ff_ops"
  let ?of_int = "arith_ops_record.of_int ff_ops"
  from 1(2) 1(1) show ?case
  proof (induct ys ys' arbitrary: xs xs' n rule: list_all2_induct)   
    case (Cons y ys y' ys' xs xs' n)
    note trans[transfer_rule] = Cons(1,2,4)
    obtain clar0 clar1 clar2 where clarify: "\<And> s u. gcd_poly_i ff_ops u
                         (minus_poly_i ff_ops y
                        (if s = 0 then [] else [?of_int (int s)])) = clar0 s u" 
        "[0..<nat p] = clar1"
        "[?on] = clar2" by auto
    define facts where "facts = concat (map (\<lambda>u. concat
                        (map (\<lambda>s. if gcd_poly_i ff_ops u
                                      (minus_poly_i ff_ops y (if s = 0 then [] else [?of_int (int s)])) \<noteq>
                                     [?on]
                                  then [gcd_poly_i ff_ops u
                                         (minus_poly_i ff_ops y (if s = 0 then [] else [?of_int (int s)]))]
                                  else [])
                          [0..<nat p])) xs)"
    define Facts where "Facts = [w\<leftarrow>concat
                          (map (\<lambda>u. map (\<lambda>s. gcd_poly_i ff_ops u
                                              (minus_poly_i ff_ops y
                                                (if s = 0 then [] else [?of_int (int s)])))
                                     [0..<nat p])
                            xs) .  w \<noteq> [?on]]"
    have Facts: "Facts = facts"
      unfolding Facts_def facts_def clarify
    proof (induct xs)
      case (Cons x xs)
      show ?case by (simp add: Cons, induct clar1, auto)
    qed simp
    define facts' where "facts' = concat
             (map (\<lambda>u. concat
                        (map (\<lambda>x. if gcd u (y' - [:of_nat x:]) \<noteq> 1
                                  then [gcd u (y' - [:of_int (int x):])] else [])
                          [0..<nat p]))
               xs')" 
    have id: "\<And> x. of_int (int x) = of_nat x" "[?on] = one_poly_i ff_ops" 
      by (auto simp: one_poly_i_def) 
    have facts[transfer_rule]: "list_all2 poly_rel facts facts'"
      unfolding facts_def facts'_def
    apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
    apply (rule list.map_transfer[unfolded rel_fun_def, rule_format, OF _ trans(3)])
    apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
    apply (rule list_all2_map_map)
    proof (unfold id)
      fix f f' x
      assume [transfer_rule]: "poly_rel f f'" and x: "x \<in> set [0..<nat p]"
      hence *: "0 \<le> int x" "int x < p" by auto
      from of_int[OF this] have rel[transfer_rule]: "R (?of_int (int x)) (of_nat x)" by auto
      {
        assume "0 < x" 
        with * have *: "0 < int x" "int x < p" by auto
        have "(of_nat x :: 'a mod_ring) = of_int (int x)" by simp
        also have "\<dots> \<noteq> 0" unfolding of_int_of_int_mod_ring using * unfolding p
          by (transfer', auto)
      }
      with rel have [transfer_rule]: "poly_rel (if x = 0 then [] else [?of_int (int x)]) [:of_nat x:]"
        unfolding poly_rel_def by (auto simp add: cCons_def p)
      show "list_all2 poly_rel
          (if gcd_poly_i ff_ops f (minus_poly_i ff_ops y (if x = 0 then [] else [?of_int (int x)])) \<noteq> one_poly_i ff_ops
           then [gcd_poly_i ff_ops f (minus_poly_i ff_ops y (if x = 0 then [] else [?of_int (int x)]))]
           else [])
          (if gcd f' (y' - [:of_nat x:]) \<noteq> 1 then [gcd f' (y' - [:of_nat x:])] else [])"
        by transfer_prover
    qed
    have id1: "berlekamp_factorization_main_i p ff_ops ?ze ?on d xs (y # ys) n = (
      if y = [?on] then berlekamp_factorization_main_i p ff_ops ?ze ?on d xs ys n else
      if length xs = n then xs else
      (let fac = facts;
          (lin, nonlin) = List.partition (\<lambda>q. degree_i q = d) fac
             in lin @ berlekamp_factorization_main_i p ff_ops ?ze ?on d nonlin ys (n - length lin)))" 
      unfolding berlekamp_factorization_main_i.simps Facts[symmetric]
      by (simp add: o_def Facts_def Let_def)
    have id2: "berlekamp_factorization_main d xs' (y' # ys') n = (
      if y' = 1 then berlekamp_factorization_main d xs' ys' n
      else if length xs' = n then xs' else
      (let fac = facts';
          (lin, nonlin) = List.partition (\<lambda>q. degree q = d) fac
              in lin @ berlekamp_factorization_main d nonlin ys' (n - length lin)))"
      by (simp add: o_def facts'_def nat_p)
    have len: "length xs = length xs'" by transfer_prover
    have id3: "(y = [?on]) = (y' = 1)" 
      by (transfer_prover_start, transfer_step+, simp add: one_poly_i_def finite_field_ops_int_def)
    show ?case
    proof (cases "y' = 1")
      case True
      hence id4: "(y' = 1) = True" by simp
      show ?thesis unfolding id1 id2 id3 id4 if_True
        by (rule Cons(3), transfer_prover)
    next
      case False
      hence id4: "(y' = 1) = False" by simp
      note id1 = id1[unfolded id3 id4 if_False]
      note id2 = id2[unfolded id4 if_False]
      show ?thesis
      proof (cases "length xs' = n")
        case True
        thus ?thesis unfolding id1 id2 Let_def len using trans by simp
      next
        case False
        hence id: "(length xs' = n) = False" by simp
        have id': "length [q\<leftarrow>facts . degree_i q = d] = length [q\<leftarrow>facts'. degree q = d]" 
          by transfer_prover   
        have [transfer_rule]: "list_all2 poly_rel (berlekamp_factorization_main_i p ff_ops ?ze ?on d [x\<leftarrow>facts . degree_i x \<noteq> d] ys
         (n - length [q\<leftarrow>facts . degree_i q = d])) 
         (berlekamp_factorization_main d [x\<leftarrow>facts' . degree x \<noteq> d] ys'
         (n - length [q\<leftarrow>facts' . degree q = d]))"
          unfolding id'
          by (rule Cons(3), transfer_prover)
        show ?thesis unfolding id1 id2 Let_def len id if_False
          unfolding partition_filter_conv o_def split by transfer_prover
      qed
    qed
  qed simp
qed
    
lemma berlekamp_monic_factorization_i[transfer_rule]: 
  "((=) ===> poly_rel ===> list_all2 poly_rel) 
     (berlekamp_monic_factorization_i p ff_ops) berlekamp_monic_factorization" 
  unfolding berlekamp_monic_factorization_i_def[abs_def] berlekamp_monic_factorization_def[abs_def] Let_def
  by transfer_prover

lemma dist_degree_factorize_main_i: 
  "poly_rel F f \<Longrightarrow> poly_rel G g \<Longrightarrow> list_all2 (rel_prod (=) poly_rel) Res res 
   \<Longrightarrow> list_all2 (rel_prod (=) poly_rel) 
      (dist_degree_factorize_main_i p ff_ops 
         (arith_ops_record.zero ff_ops) (arith_ops_record.one ff_ops) (degree_i F) F G d Res)
      (dist_degree_factorize_main f g d res)" 
proof (induct f g d res arbitrary: F G Res rule: dist_degree_factorize_main.induct)
  case (1 v w d res V W Res)
  let ?ze = "arith_ops_record.zero ff_ops" 
  let ?on = "arith_ops_record.one ff_ops"
  note simp = dist_degree_factorize_main.simps[of v w d] 
    dist_degree_factorize_main_i.simps[of p ff_ops ?ze ?on "degree_i V" V W d]
  have v[transfer_rule]: "poly_rel V v" by (rule 1)
  have w[transfer_rule]: "poly_rel W w" by (rule 1)
  have res[transfer_rule]: "list_all2 (rel_prod (=) poly_rel) Res res" by (rule 1)
  have [transfer_rule]: "poly_rel [?on] 1"
    by (simp add: one poly_rel_def)
  have id1: "(V = [?on]) = (v = 1)" unfolding finite_field_ops_int_def by transfer_prover
  have id2: "degree_i V = degree v" by transfer_prover
  note simp = simp[unfolded id1 id2]
  note IH = 1(1,2)
  show ?case 
  proof (cases "v = 1")
    case True
    with res show ?thesis unfolding id2 simp by simp
  next
    case False
    with id1 have "(v = 1) = False" by auto
    note simp = simp[unfolded this if_False]
    note IH = IH[OF False]
    show ?thesis
    proof (cases "degree v < d + d")
      case True
      thus ?thesis unfolding id2 simp using res v by auto
    next
      case False
      hence "(degree v < d + d) = False" by auto
      note simp = simp[unfolded this if_False]
      let ?P = "power_poly_f_mod_i ff_ops (\<lambda>f. mod_field_poly_i ff_ops f V) W (nat p)" 
      let ?G = "gcd_poly_i ff_ops (minus_poly_i ff_ops ?P [?ze, ?on]) V" 
      let ?g = "gcd (w ^ CARD('a) mod v - monom 1 1) v" 
      define G where "G = ?G" 
      define g where "g = ?g"
      note simp = simp[unfolded Let_def, folded G_def g_def]
      note IH = IH[OF False refl refl refl]
      have [transfer_rule]: "poly_rel [?ze,?on] (monom 1 1)" unfolding poly_rel_def
        by (auto simp: coeffs_monom one zero)
      have id: "w ^ CARD('a) mod v = power_poly_f_mod v w (nat p)"
        unfolding power_poly_f_mod_def by (simp add: p)
      have P[transfer_rule]: "poly_rel ?P (w ^ CARD('a) mod v)" unfolding id
        by (rule power_poly_f_mod_i[OF _ w], transfer_prover)
      have g[transfer_rule]: "poly_rel G g" unfolding G_def g_def by transfer_prover
      have id3: "(G = [?on]) = (g = 1)" by transfer_prover
      note simp = simp[unfolded id3]
      show ?thesis
      proof (cases "g = 1")
        case True
        from IH(1)[OF this[unfolded g_def] v P res] True
        show ?thesis unfolding id2 simp by simp
      next
        case False
        have vg: "poly_rel (div_field_poly_i ff_ops V G) (v div g)" by transfer_prover
        have "poly_rel (mod_field_poly_i ff_ops ?P
          (div_field_poly_i ff_ops V G)) (w ^ CARD('a) mod v mod (v div g))" by transfer_prover        
        note IH = IH(2)[OF False[unfolded g_def] refl vg[unfolded G_def g_def] this[unfolded G_def g_def],
            folded g_def G_def]
        have "list_all2 (rel_prod (=) poly_rel) ((Suc d, G) # Res) ((Suc d, g) # res)" 
          using g res by auto
        note IH = IH[OF this]
        from False have "(g = 1) = False" by simp
        note simp = simp[unfolded this if_False]
        show ?thesis unfolding id2 simp using IH by simp
      qed
    qed
  qed
qed
      
lemma distinct_degree_factorization_i[transfer_rule]: "(poly_rel ===> list_all2 (rel_prod (=) poly_rel)) 
  (distinct_degree_factorization_i p ff_ops) distinct_degree_factorization"
proof 
  fix F f
  assume f[transfer_rule]: "poly_rel F f" 
  have id: "(degree_i F = 1) = (degree f = 1)" by transfer_prover
  note d = distinct_degree_factorization_i_def distinct_degree_factorization_def
  let ?ze = "arith_ops_record.zero ff_ops" 
  let ?on = "arith_ops_record.one ff_ops"
  show "list_all2 (rel_prod (=) poly_rel) (distinct_degree_factorization_i p ff_ops F)
            (distinct_degree_factorization f)" 
  proof (cases "degree f = 1")
    case True
    with id f show ?thesis unfolding d by auto
  next
    case False
    from False id have "?thesis = (list_all2 (rel_prod (=) poly_rel) 
      (dist_degree_factorize_main_i p ff_ops ?ze ?on (degree_i F) F [?ze, ?on] 0 [])
      (dist_degree_factorize_main f (monom 1 1) 0 []))" unfolding d Let_def by simp    
    also have \<dots>
      by (rule dist_degree_factorize_main_i[OF f], auto simp: poly_rel_def
        coeffs_monom one zero)
    finally show ?thesis .
  qed
qed

lemma finite_field_factorization_i[transfer_rule]: 
  "(poly_rel ===> rel_prod R (list_all2 poly_rel))
     (finite_field_factorization_i p ff_ops) finite_field_factorization" 
  unfolding finite_field_factorization_i_def finite_field_factorization_def Let_def lead_coeff_i_def'
  by transfer_prover

text \<open>Since the implementation is sound, we can now combine it with the soundness result
  of the finite field factorization.\<close>

lemma finite_field_i_sound: 
  assumes f': "f' = of_int_poly_i ff_ops (Mp f)" 
  and berl_i: "finite_field_factorization_i p ff_ops f' = (c',fs')"
  and sq: "square_free_m f" 
  and fs: "fs = map (to_int_poly_i ff_ops) fs'"
  and c: "c = arith_ops_record.to_int ff_ops c'" 
  shows "unique_factorization_m f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
proof -
  define f'' :: "'a mod_ring poly" where "f'' = of_int_poly (Mp f)"
  have rel_f[transfer_rule]: "poly_rel f' f''" 
    by (rule poly_rel_of_int_poly[OF f'], simp add: f''_def)
  interpret pff: idom_ops "poly_ops ff_ops" poly_rel 
    by (rule idom_ops_poly)
  obtain c'' fs'' where berl: "finite_field_factorization f'' = (c'',fs'')" by force
  from rel_funD[OF finite_field_factorization_i rel_f, unfolded rel_prod_conv assms(2) split berl]
  have rel[transfer_rule]: "R c' c''" "list_all2 poly_rel fs' fs''" by auto  
  from to_int[OF rel(1)] have cc': "c = to_int_mod_ring c''" unfolding c by simp
  have c: "c \<in> {0 ..< p}" unfolding cc'
    by (metis Divides.pos_mod_bound Divides.pos_mod_sign M_to_int_mod_ring atLeastLessThan_iff 
      gr_implies_not_zero nat_le_0 nat_p not_le poly_mod.M_def zero_less_card_finite)
  {
    fix f
    assume "f \<in> set fs'" 
    with rel(2) obtain f' where "poly_rel f f'"  unfolding list_all2_conv_all_nth set_conv_nth
      by auto
    hence "is_poly ff_ops f" using fun_cong[OF Domainp_is_poly, of f]
      unfolding Domainp_iff[abs_def] by auto
  }
  hence fs': "Ball (set fs') (is_poly ff_ops)" by auto
  define mon :: "'a mod_ring poly \<Rightarrow> bool" where "mon = monic"
  have [transfer_rule]: "(poly_rel ===> (=)) (monic_i ff_ops) mon" unfolding mon_def 
    by (rule poly_rel_monic)
  have len: "length fs' = length fs''" by transfer_prover
  have fs': "fs = map to_int_poly fs''" unfolding fs 
  proof (rule nth_map_conv[OF len], intro allI impI)
    fix i
    assume i: "i < length fs'" 
    obtain f g where id: "fs' ! i = f" "fs'' ! i = g" by auto
    from i rel(2)[unfolded list_all2_conv_all_nth[of _ fs' fs'']] id
    have "poly_rel f g" by auto
    from to_int_poly_i[OF this] have "to_int_poly_i ff_ops f = to_int_poly g" .
    thus "to_int_poly_i ff_ops (fs' ! i) = to_int_poly (fs'' ! i)" unfolding id .
  qed
  have f: "f'' = of_int_poly f" unfolding poly_eq_iff f''_def
    by (simp add: to_int_mod_ring_hom.injectivity to_int_mod_ring_of_int_M Mp_coeff)
  have *: "unique_factorization_m f (c, mset fs)" 
    using finite_field_factorization_modulo_ring[OF f sq berl cc' fs'] by auto
  have fs': "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})" unfolding fs' 
    using range_to_int_mod_ring[where 'a = 'a]
    by (auto simp: coeffs_to_int_poly p)
  with c fs *
  show ?thesis by blast
qed
end

definition finite_field_factorization_main :: "int \<Rightarrow> 'i arith_ops_record \<Rightarrow> int poly \<Rightarrow> int \<times> int poly list" where
  "finite_field_factorization_main p f_ops f \<equiv> 
    let (c',fs') = finite_field_factorization_i p f_ops (of_int_poly_i f_ops (poly_mod.Mp p f))
      in (arith_ops_record.to_int f_ops c', map (to_int_poly_i f_ops) fs')"

lemma(in prime_field_gen) finite_field_factorization_main: 
  assumes res: "finite_field_factorization_main p ff_ops f = (c,fs)"
  and sq: "square_free_m f" 
  shows "unique_factorization_m f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})"
proof -
  obtain c' fs' where 
    res': "finite_field_factorization_i p ff_ops (of_int_poly_i ff_ops (Mp f)) = (c', fs')"  by force
  show ?thesis  
    by (rule finite_field_i_sound[OF refl res' sq], 
      insert res[unfolded finite_field_factorization_main_def res'], auto)
qed

definition finite_field_factorization_int :: "int \<Rightarrow> int poly \<Rightarrow> int \<times> int poly list" where
  "finite_field_factorization_int p = (  
    if p \<le> 65535 
    then finite_field_factorization_main p (finite_field_ops32 (uint32_of_int p))
    else if p \<le> 4294967295
    then finite_field_factorization_main p (finite_field_ops64 (uint64_of_int p))
    else finite_field_factorization_main p (finite_field_ops_integer (integer_of_int p)))"

context poly_mod_prime begin
lemmas finite_field_factorization_main_integer = prime_field_gen.finite_field_factorization_main
  [OF prime_field.prime_field_finite_field_ops_integer, unfolded prime_field_def mod_ring_locale_def,
  unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas finite_field_factorization_main_uint32 = prime_field_gen.finite_field_factorization_main
  [OF prime_field.prime_field_finite_field_ops32, unfolded prime_field_def mod_ring_locale_def,
  unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas finite_field_factorization_main_uint64 = prime_field_gen.finite_field_factorization_main
  [OF prime_field.prime_field_finite_field_ops64, unfolded prime_field_def mod_ring_locale_def,
  unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemma finite_field_factorization_int:
  assumes sq: "poly_mod.square_free_m p f" 
  and result: "finite_field_factorization_int p f = (c,fs)"
  shows "poly_mod.unique_factorization_m p f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
  using finite_field_factorization_main_integer[OF  _ sq, of c fs]
    finite_field_factorization_main_uint32[OF _ _ sq, of c fs]
    finite_field_factorization_main_uint64[OF _ _ sq, of c fs]
    result[unfolded finite_field_factorization_int_def]
  by (auto split: if_splits)

end

end
