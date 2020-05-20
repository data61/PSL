(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>The Berlekamp Algorithm\<close>

theory Berlekamp_Type_Based
imports
  Jordan_Normal_Form.Matrix_Kernel
  Jordan_Normal_Form.Gauss_Jordan_Elimination
  Jordan_Normal_Form.Missing_VectorSpace
  Polynomial_Factorization.Square_Free_Factorization
  Polynomial_Factorization.Missing_Multiset
  Finite_Field
  Chinese_Remainder_Poly
  Poly_Mod_Finite_Field
  "HOL-Computational_Algebra.Field_as_Ring"
begin

hide_const (open) up_ring.coeff up_ring.monom Modules.module subspace
  Modules.module_hom


subsection \<open>Auxiliary lemmas\<close>

context
  fixes g :: "'b \<Rightarrow> 'a :: comm_monoid_mult"
begin
lemma prod_list_map_filter: "prod_list (map g (filter f xs)) * prod_list (map g (filter (\<lambda> x. \<not> f x) xs)) 
  = prod_list (map g xs)"
  by (induct xs, auto simp: ac_simps)

lemma prod_list_map_partition: 
  assumes "List.partition f xs = (ys, zs)"
  shows "prod_list (map g xs) = prod_list (map g ys) * prod_list (map g zs)"
  using assms  by (subst prod_list_map_filter[symmetric, of _ f], auto simp: o_def)
end

lemma coprime_id_is_unit:
  fixes a::"'b::semiring_gcd"
  shows "coprime a a \<longleftrightarrow> is_unit a"
  using dvd_unit_imp_unit by auto

lemma dim_vec_of_list[simp]: "dim_vec (vec_of_list x) = length x"
  by (transfer, auto)

lemma length_list_of_vec[simp]: "length (list_of_vec A) = dim_vec A"
  by (transfer', auto)

lemma list_of_vec_vec_of_list[simp]: "list_of_vec (vec_of_list a) = a"
proof -
  {
  fix aa :: "'a list"
  have "map (\<lambda>n. if n < length aa then aa ! n else undef_vec (n - length aa)) [0..<length aa]
    = map ((!) aa) [0..<length aa]"
    by simp
  hence "map (\<lambda>n. if n < length aa then aa ! n else undef_vec (n - length aa)) [0..<length aa] = aa"
    by (simp add: map_nth)
  }
  thus ?thesis by (transfer, simp add: mk_vec_def)
qed


context
assumes "SORT_CONSTRAINT('a::finite)"
begin

lemma inj_Poly_list_of_vec': "inj_on (Poly \<circ> list_of_vec) {v. dim_vec v = n}"
proof (rule comp_inj_on)
  show "inj_on list_of_vec {v. dim_vec v = n}"
    by (auto simp add: inj_on_def, transfer, auto simp add: mk_vec_def)
  show "inj_on Poly (list_of_vec ` {v. dim_vec v = n})"
  proof (auto simp add: inj_on_def)
    fix x y::"'c vec" assume "n = dim_vec x" and dim_xy: "dim_vec y = dim_vec x"
    and Poly_eq: "Poly (list_of_vec x) = Poly (list_of_vec y)"
    note [simp del] = nth_list_of_vec
    show "list_of_vec x = list_of_vec y"  
    proof (rule nth_equalityI, auto simp: dim_xy)
      have length_eq: "length (list_of_vec x ) = length (list_of_vec y)"
        using dim_xy by (transfer, auto)
      fix i assume "i < dim_vec x"
      thus "list_of_vec x ! i = list_of_vec y ! i" using Poly_eq unfolding poly_eq_iff coeff_Poly_eq
        using dim_xy unfolding nth_default_def by (auto, presburger)
     qed
  qed
qed

corollary inj_Poly_list_of_vec: "inj_on (Poly \<circ> list_of_vec) (carrier_vec n)"
  using inj_Poly_list_of_vec' unfolding carrier_vec_def .

lemma list_of_vec_rw_map: "list_of_vec m = map (\<lambda>n. m $ n) [0..<dim_vec m]"
    by (transfer, auto simp add: mk_vec_def)

lemma degree_Poly':
assumes xs: "xs \<noteq> []"
shows "degree (Poly xs) < length xs"
using xs
by (induct xs, auto intro: Poly.simps(1))

lemma vec_of_list_list_of_vec[simp]: "vec_of_list (list_of_vec a) = a"
by (transfer, auto simp add: mk_vec_def)

lemma row_mat_of_rows_list:
assumes b: "b < length A"
and nc: "\<forall>i. i < length A \<longrightarrow> length (A ! i) = nc"
shows "(row (mat_of_rows_list nc A) b) = vec_of_list (A ! b)"
proof (auto simp add: vec_eq_iff)
  show "dim_col (mat_of_rows_list nc A) = length (A ! b)"
    unfolding mat_of_rows_list_def using b nc by auto
  fix i assume i: "i < length (A ! b)"
  show "row (mat_of_rows_list nc A) b $ i = vec_of_list (A ! b) $ i"
    using i b nc
    unfolding mat_of_rows_list_def row_def
    by (transfer, auto simp add: mk_vec_def mk_mat_def)
qed

lemma degree_Poly_list_of_vec:
assumes n: "x \<in> carrier_vec n"
and n0: "n > 0"
shows "degree (Poly (list_of_vec x)) < n"
proof -
  have x_dim: "dim_vec x = n" using n by auto
  have l: "(list_of_vec x) \<noteq> []"
    by (auto simp add: list_of_vec_rw_map vec_of_dim_0[symmetric] n0 n x_dim)
  have "degree (Poly (list_of_vec x)) < length (list_of_vec x)" by (rule degree_Poly'[OF l])
  also have "... = n" using x_dim by auto
  finally show ?thesis .
qed

lemma list_of_vec_nth:
  assumes i: "i < dim_vec x"
  shows "list_of_vec x ! i = x $ i"
  using i
  by (transfer, auto simp add: mk_vec_def)

lemma coeff_Poly_list_of_vec_nth':
 assumes i: "i < dim_vec x"
 shows "coeff (Poly (list_of_vec x)) i = x $ i"
 using i
 by (auto simp add: list_of_vec_nth nth_default_def)

lemma list_of_vec_row_nth:
assumes x: "x < dim_col A"
shows "list_of_vec (row A i) ! x = A $$ (i, x)"
using x unfolding row_def by (transfer', auto simp add: mk_vec_def)

lemma coeff_Poly_list_of_vec_nth:
assumes x: "x < dim_col A"
shows "coeff (Poly (list_of_vec (row A i))) x = A $$ (i, x)"
proof -
  have "coeff (Poly (list_of_vec (row A i))) x  = nth_default 0 (list_of_vec (row A i)) x"
    unfolding coeff_Poly_eq  by simp
  also have "... = A $$ (i, x)" using x list_of_vec_row_nth
    unfolding nth_default_def by (auto simp del: nth_list_of_vec)
  finally show ?thesis .
qed

lemma inj_on_list_of_vec: "inj_on list_of_vec (carrier_vec n)"
 unfolding inj_on_def unfolding list_of_vec_rw_map by auto

lemma vec_of_list_carrier[simp]: "vec_of_list x \<in> carrier_vec (length x)"
  unfolding carrier_vec_def by simp

lemma card_carrier_vec: "card (carrier_vec n:: 'b::finite vec set) = CARD('b) ^ n"
proof -
  let ?A = "UNIV::'b set"
  let ?B = "{xs. set xs \<subseteq> ?A \<and> length xs = n}"
  let ?C = "(carrier_vec n:: 'b::finite vec set)"
  have "card ?C = card ?B"
  proof -
    have "bij_betw (list_of_vec) ?C ?B"
    proof (unfold bij_betw_def, auto)
      show "inj_on list_of_vec (carrier_vec n)" by (rule inj_on_list_of_vec)
      fix x::"'b list"
      assume n: "n = length x"
      thus "x \<in> list_of_vec ` carrier_vec (length x)"
        unfolding image_def
        by auto (rule bexI[of _ "vec_of_list x"], auto)
    qed
    thus ?thesis using bij_betw_same_card by blast
  qed
  also have "... = card ?A ^ n"
    by (rule card_lists_length_eq, simp)
  finally show ?thesis .
qed


lemma finite_carrier_vec[simp]: "finite (carrier_vec n:: 'b::finite vec set)"
  by (rule card_ge_0_finite, unfold card_carrier_vec, auto)


lemma row_echelon_form_dim0_row:
assumes "A \<in> carrier_mat 0 n"
shows "row_echelon_form A"
using assms
unfolding row_echelon_form_def pivot_fun_def Let_def by auto

lemma row_echelon_form_dim0_col:
assumes "A \<in> carrier_mat n 0"
shows "row_echelon_form A"
using assms
unfolding row_echelon_form_def pivot_fun_def Let_def by auto

lemma row_echelon_form_one_dim0[simp]: "row_echelon_form (1\<^sub>m 0)"
  unfolding row_echelon_form_def pivot_fun_def Let_def by auto

lemma Poly_list_of_vec_0[simp]: "Poly (list_of_vec (0\<^sub>v 0)) = [:0:]"
  by (simp add: poly_eq_iff nth_default_def)

lemma monic_normalize:
assumes "(p :: 'b :: {field,euclidean_ring_gcd} poly) \<noteq> 0" shows "monic (normalize p)"
by (simp add: assms normalize_poly_old_def)


lemma exists_factorization_prod_list:
fixes P::"'b::field poly list"
assumes "degree (prod_list P) > 0"
  and "\<And> u. u \<in> set P \<Longrightarrow> degree u > 0 \<and> monic u"
  and "square_free (prod_list P)"
shows "\<exists>Q. prod_list Q = prod_list P \<and> length P \<le> length Q
           \<and> (\<forall>u. u \<in> set Q \<longrightarrow> irreducible u \<and> monic u)"
using assms
proof (induct P)
  case Nil
  thus ?case by auto
next
  case (Cons x P)
  have sf_P: "square_free (prod_list P)"
    by (metis Cons.prems(3) dvd_triv_left prod_list.Cons mult.commute square_free_factor)
  have deg_x: "degree x > 0" using Cons.prems by auto
  have distinct_P: "distinct P"
    by (meson Cons.prems(2) Cons.prems(3) distinct.simps(2) square_free_prod_list_distinct)
  have "\<exists>A. finite A \<and> x = \<Prod>A \<and> A \<subseteq> {q. irreducible q \<and> monic q}"
    proof (rule monic_square_free_irreducible_factorization)
      show "monic x" by (simp add: Cons.prems(2))
      show "square_free x"
        by (metis Cons.prems(3) dvd_triv_left prod_list.Cons square_free_factor)
    qed
    from this obtain A where fin_A: "finite A"
    and xA: "x = \<Prod>A"
    and A: "A \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    by auto
    obtain A' where s: "set A' = A" and length_A': "length A' = card A"
      using \<open>finite A\<close> distinct_card finite_distinct_list by force
  have A_not_empty: "A \<noteq> {}" using xA deg_x by auto
  have x_prod_list_A': "x = prod_list A'"
  proof -
    have "x = \<Prod>A" using xA by simp
    also have "... = prod id A" by simp
    also have "... = prod id (set A')" unfolding s by simp
    also have "... = prod_list (map id A')"
      by (rule prod.distinct_set_conv_list, simp add: card_distinct length_A' s)
    also have "... =  prod_list A'" by auto
    finally show ?thesis .
  qed
  show ?case
  proof (cases "P = []")
    case True
    show ?thesis
    proof (rule exI[of _ "A'"], auto simp add: True)
      show "prod_list A' = x" using x_prod_list_A' by simp
      show "Suc 0 \<le> length A'" using A_not_empty using s length_A'
        by (simp add: Suc_leI card_gt_0_iff fin_A)
      show "\<And>u. u \<in> set A' \<Longrightarrow> irreducible u" using s A by auto
      show "\<And>u. u \<in> set A' \<Longrightarrow> monic u" using s A by auto
    qed
 next
  case False
  have hyp: "\<exists>Q. prod_list Q = prod_list P
    \<and> length P \<le> length Q \<and> (\<forall>u. u \<in> set Q \<longrightarrow> irreducible u \<and> monic u)"
  proof (rule Cons.hyps[OF _ _ sf_P])
    have set_P: "set P \<noteq> {}" using False by auto
    have "prod_list P = prod_list (map id P)" by simp
    also have "... = prod id (set P)"
      using prod.distinct_set_conv_list[OF distinct_P, of id] by simp
    also have "... = \<Prod>(set P)" by simp
    finally have "prod_list P = \<Prod>(set P)" .
    hence "degree (prod_list P) = degree (\<Prod>(set P))" by simp
    also have "... = degree (prod id (set P))" by simp
    also have "... = (\<Sum>i\<in>(set P). degree (id i))"
    proof (rule degree_prod_eq_sum_degree)
      show "\<forall>i\<in>set P. id i \<noteq> 0" using Cons.prems(2) by force
    qed
    also have "... > 0"
      by (metis Cons.prems(2) List.finite_set set_P gr0I id_apply insert_iff list.set(2) sum_pos)
    finally show "degree (prod_list P) > 0" by simp
    show "\<And>u. u \<in> set P \<Longrightarrow> degree u > 0 \<and> monic u" using Cons.prems by auto
  qed
  from this obtain Q where QP: "prod_list Q = prod_list P" and length_PQ: "length P \<le> length Q"
  and monic_irr_Q: "(\<forall>u. u \<in> set Q \<longrightarrow> irreducible u \<and> monic u)" by blast
  show ?thesis
  proof (rule exI[of _ "A' @ Q"], auto simp add: monic_irr_Q)
    show "prod_list A' * prod_list Q = x * prod_list P" unfolding QP x_prod_list_A' by auto
    have "length A' \<noteq> 0" using A_not_empty using s length_A' by auto
    thus "Suc (length P) \<le> length A' + length Q" using QP length_PQ by linarith
    show "\<And>u. u \<in> set A' \<Longrightarrow> irreducible u" using s A by auto
    show "\<And>u. u \<in> set A' \<Longrightarrow> monic u" using s A by auto
  qed
qed
qed

lemma normalize_eq_imp_smult:
  fixes p :: "'b :: {euclidean_ring_gcd} poly"
  assumes n: "normalize p = normalize q"
  shows "\<exists> c. c \<noteq> 0 \<and> q = smult c p"
proof(cases "p = 0")
  case True with n show ?thesis by (auto intro:exI[of _ 1])
next
  case p0: False
  have degree_eq: "degree p = degree q" using n degree_normalize by metis
  hence q0:  "q \<noteq> 0" using p0 n by auto
  have p_dvd_q: "p dvd q" using n by (simp add: associatedD1)
  from p_dvd_q obtain k where q: "q = k * p" unfolding dvd_def by (auto simp: ac_simps)
  with q0 have "k \<noteq> 0" by auto
  then have "degree k = 0"
    using degree_eq degree_mult_eq p0 q by fastforce
  then obtain c where k: "k = [: c :]" by (metis degree_0_id)
  with \<open>k \<noteq> 0\<close> have "c \<noteq> 0" by auto
  have "q = smult c p" unfolding q k by simp
  with \<open>c \<noteq> 0\<close> show ?thesis by auto
qed

lemma prod_list_normalize: 
  fixes P :: "'b :: {idom_divide,normalization_semidom_multiplicative} poly list"
  shows "normalize (prod_list P) = prod_list (map normalize P)"
proof (induct P)
  case Nil
  show ?case by auto
next
  case (Cons p P)
  have "normalize (prod_list (p # P)) = normalize p * normalize (prod_list P)"
    using normalize_mult by auto
  also have "... = normalize p * prod_list (map normalize P)" using Cons.hyps by auto
  also have "... = prod_list (normalize p # (map normalize P))" by auto
  also have "... = prod_list (map normalize (p # P))" by auto
  finally show ?case .
qed


lemma prod_list_dvd_prod_list_subset:
fixes A::"'b::comm_monoid_mult list"
assumes dA: "distinct A"
  and dB: "distinct B" (*Maybe this condition could be avoided*)
  and s: "set A \<subseteq> set B"
shows "prod_list A dvd prod_list B"
proof -
  have "prod_list A = prod_list (map id A)" by auto
  also have "... = prod id (set A)"
    by (rule prod.distinct_set_conv_list[symmetric, OF dA])
  also have "... dvd prod id (set B)"
    by (rule prod_dvd_prod_subset[OF _ s], auto)
  also have "... = prod_list (map id B)"
    by (rule prod.distinct_set_conv_list[OF dB])
  also have "... = prod_list B" by simp
  finally show ?thesis .
qed

end

lemma gcd_monic_constant:
  "gcd f g \<in> {1, f}" if "monic f" and "degree g = 0"
    for f g :: "'a :: {field_gcd} poly"
proof (cases "g = 0")
  case True
  moreover from \<open>monic f\<close> have "normalize f = f"
    by (rule normalize_monic)
  ultimately show ?thesis
    by simp
next
  case False
  with \<open>degree g = 0\<close> have "is_unit g"
    by simp
  then have "Rings.coprime f g"
    by (rule is_unit_right_imp_coprime)
  then show ?thesis
    by simp
qed

lemma distinct_find_base_vectors:
fixes A::"'a::field mat"
assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier_mat nr nc"
shows "distinct (find_base_vectors A)"
proof -
  note non_pivot_base = non_pivot_base[OF ref A]
  let ?pp = "set (pivot_positions A)"
  from A have dim: "dim_row A = nr" "dim_col A = nc" by auto
  {
    fix j j'
    assume j: "j < nc" "j \<notin> snd ` ?pp" and j': "j' < nc" "j' \<notin> snd ` ?pp" and neq: "j' \<noteq> j"
    from non_pivot_base(2)[OF j] non_pivot_base(4)[OF j' j neq]
    have "non_pivot_base A (pivot_positions A) j \<noteq> non_pivot_base A (pivot_positions A) j'" by auto
  }
  hence inj: "inj_on (non_pivot_base A (pivot_positions A))
     (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` ?pp])" unfolding inj_on_def by auto
  thus ?thesis unfolding  find_base_vectors_def Let_def unfolding distinct_map dim by auto
qed

lemma length_find_base_vectors:
fixes A::"'a::field mat"
assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier_mat nr nc"
shows "length (find_base_vectors A) = card (set (find_base_vectors A))"
using  distinct_card[OF distinct_find_base_vectors[OF ref A]] by auto


subsection \<open>Previous Results\<close>

definition power_poly_f_mod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "power_poly_f_mod modulus = (\<lambda>a n. a ^ n mod modulus)"

lemma power_poly_f_mod_binary: "power_poly_f_mod m a n = (if n = 0 then 1 mod m
    else let (d, r) = Divides.divmod_nat n 2;
       rec = power_poly_f_mod m ((a * a) mod m) d in
    if r = 0 then rec else (rec * a) mod m)"
  for m a :: "'a :: {field_gcd} poly"
proof -
  note d = power_poly_f_mod_def
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis unfolding d by simp
  next
    case False
    obtain q r where div: "Divides.divmod_nat n 2 = (q,r)" by force
    hence n: "n = 2 * q + r" and r: "r = 0 \<or> r = 1" unfolding divmod_nat_def by auto
    have id: "a ^ (2 * q) = (a * a) ^ q"
      by (simp add: power_mult_distrib semiring_normalization_rules)
    show ?thesis
    proof (cases "r = 0")
      case True
      show ?thesis
        using power_mod [of "a * a" m q]
        by (auto simp add: divmod_nat_def Let_def True n d div id)
    next
      case False
      with r have r: "r = 1" by simp
      show ?thesis
        by (auto simp add: d r div Let_def mod_simps)
          (simp add: n r mod_simps ac_simps power_mult_distrib power_mult power2_eq_square)
    qed
  qed
qed


fun power_polys where
  "power_polys mul_p u curr_p (Suc i) = curr_p #
      power_polys mul_p u ((curr_p * mul_p) mod u) i"
| "power_polys mul_p u curr_p 0 = []"

context
assumes "SORT_CONSTRAINT('a::prime_card)"
begin

lemma fermat_theorem_mod_ring [simp]:
  fixes a::"'a mod_ring"
  shows "a ^ CARD('a) = a"
proof (cases "a = 0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
  proof transfer
    fix a
    assume "a \<in> {0..<int CARD('a)}" and "a \<noteq> 0"
    then have a: "1 \<le> a" "a < int CARD('a)"
      by simp_all
    then have [simp]: "a mod int CARD('a) = a"
      by simp
    from a have "\<not> int CARD('a) dvd a"
      by (auto simp add: zdvd_not_zless)
    then have "\<not> CARD('a) dvd nat \<bar>a\<bar>"
      by simp
    with a have "\<not> CARD('a) dvd nat a"
      by simp
    with prime_card have "[nat a ^ (CARD('a) - 1) = 1] (mod CARD('a))"
      by (rule fermat_theorem)
    with a have "int (nat a ^ (CARD('a) - 1) mod CARD('a)) = 1"
      by (simp add: cong_def)
    with a have "a ^ (CARD('a) - 1) mod CARD('a) = 1"
      by (simp add: of_nat_mod)
    then have "a * (a ^ (CARD('a) - 1) mod int CARD('a)) = a"
      by simp
    then have "(a * (a ^ (CARD('a) - 1) mod int CARD('a))) mod int CARD('a) = a mod int CARD('a)"
      by (simp only:)
    then show "a ^ CARD('a) mod int CARD('a) = a"
      by (simp add: mod_simps semiring_normalization_rules(27))
  qed
qed


lemma mod_eq_dvd_iff_poly: "((x::'a mod_ring poly) mod n = y mod n) = (n dvd x - y)"
proof
  assume H: "x mod n = y mod n"
  hence "x mod n - y mod n = 0" by simp
  hence "(x mod n - y mod n) mod n = 0" by simp
  hence "(x - y) mod n = 0" by (simp add: mod_diff_eq)
  thus "n dvd x - y" by (simp add: dvd_eq_mod_eq_0)
next
  assume H: "n dvd x - y"
  then obtain k where k: "x-y = n*k" unfolding dvd_def by blast
  hence "x = n*k + y" using diff_eq_eq by blast
  hence "x mod n = (n*k + y) mod n" by simp
  thus "x mod n = y mod n" by (simp add: mod_add_left_eq)
qed

lemma cong_gcd_eq_poly:
  "gcd a m = gcd b m" if "[(a::'a mod_ring poly) = b] (mod m)"
  using that by (simp add: cong_def) (metis gcd_mod_left mod_by_0)

lemma coprime_h_c_poly:
fixes h::"'a mod_ring poly"
assumes "c1 \<noteq> c2"
shows "coprime (h - [:c1:]) (h - [:c2:])"
proof (intro coprimeI)
  fix d assume "d dvd h - [:c1:]"
  and "d dvd h - [:c2:]"
  hence "h mod d = [:c1:] mod d" and "h mod d = [:c2:] mod d"
    using mod_eq_dvd_iff_poly by simp+
  hence "[:c1:] mod d = [:c2:] mod d" by simp
  hence "d dvd [:c2 - c1:]"
    by (metis (no_types) mod_eq_dvd_iff_poly diff_pCons right_minus_eq)
  thus "is_unit d"
    by (metis (no_types) assms dvd_trans is_unit_monom_0 monom_0 right_minus_eq)
qed


lemma coprime_h_c_poly2:
fixes h::"'a mod_ring poly"
assumes "coprime (h - [:c1:]) (h - [:c2:])"
and "\<not> is_unit (h - [:c1:])"
shows "c1 \<noteq> c2"
using assms coprime_id_is_unit by blast


lemma degree_minus_eq_right:
fixes p::"'b::ab_group_add poly"
shows "degree q < degree p \<Longrightarrow> degree (p - q) = degree p"
using degree_add_eq_left[of "-q" p] degree_minus by auto

lemma coprime_prod:
  fixes A::"'a mod_ring set" and g::"'a mod_ring \<Rightarrow> 'a mod_ring poly"
  assumes "\<forall>x\<in>A. coprime (g a) (g x)"
  shows "coprime (g a) (prod (\<lambda>x. g x) A)"
proof -
  have f: "finite A" by simp
  show ?thesis
  using f using assms
  proof (induct A)
    case (insert x A)
    have "(\<Prod>c\<in>insert x A. g c) = (g x) * (\<Prod>c\<in>A. g c)"
      by (simp add: insert.hyps(2))
    with insert.prems show ?case
      by (auto simp: insert.hyps(3) prod_coprime_right)
  qed auto
qed


lemma coprime_prod2:
  fixes A::"'b::semiring_gcd set"
  assumes "\<forall>x\<in>A. coprime (a) (x)" and f: "finite A"
  shows "coprime (a) (prod (\<lambda>x. x) A)"
  using f using assms
proof (induct A)
  case (insert x A)
  have "(\<Prod>c\<in>insert x A. c) = (x) * (\<Prod>c\<in>A. c)"
    by (simp add: insert.hyps)
  with insert.prems show ?case
    by (simp add: insert.hyps prod_coprime_right)
qed auto



lemma divides_prod:
  fixes g::"'a mod_ring \<Rightarrow> 'a mod_ring poly"
  assumes "\<forall>c1 c2. c1 \<in> A \<and> c2 \<in> A \<and> c1 \<noteq> c2 \<longrightarrow> coprime (g c1) (g c2)"
  assumes "\<forall>c\<in> A. g c dvd f"
  shows "(\<Prod>c\<in>A. g c) dvd f"
proof -
  have finite_A: "finite A" using finite[of A] .
  thus ?thesis using assms
  proof (induct A)
    case (insert x A)
    have "(\<Prod>c\<in>insert x A. g c) =  g x * (\<Prod>c\<in> A. g c)"
      by (simp add: insert.hyps(2))
    also have "... dvd f"
    proof (rule divides_mult)
      show "g x dvd f" using insert.prems by auto
      show "prod g A dvd f" using insert.hyps(3) insert.prems by auto
      from insert show "Rings.coprime (g x) (prod g A)"
        by (auto intro: prod_coprime_right)
    qed
    finally show ?case .
   qed auto
qed

(*
  Proof of equation 9 in the book by Knuth
  x^p - x = (x-0)(x-1)...(x-(p-1))  (mod p)
*)

lemma poly_monom_identity_mod_p:
  "monom (1::'a mod_ring) (CARD('a)) - monom 1 1 = prod (\<lambda>x. [:0,1:] - [:x:]) (UNIV::'a mod_ring set)"
  (is "?lhs = ?rhs")
proof -
  let ?f="(\<lambda>x::'a mod_ring. [:0,1:] - [:x:])"
  have "?rhs dvd ?lhs"
  proof (rule divides_prod)
    {
    fix a::"'a mod_ring"
    have "poly ?lhs a = 0"
      by (simp add: poly_monom)
    hence "([:0,1:] - [:a:]) dvd ?lhs"
      using poly_eq_0_iff_dvd by fastforce
    }
    thus "\<forall>x\<in>UNIV::'a mod_ring set. [:0, 1:] - [:x:] dvd monom 1 CARD('a) - monom 1 1" by fast
    show "\<forall>c1 c2. c1 \<in> UNIV \<and> c2 \<in> UNIV \<and> c1 \<noteq> (c2 :: 'a mod_ring) \<longrightarrow> coprime ([:0, 1:] - [:c1:]) ([:0, 1:] - [:c2:])"
      by (auto dest!: coprime_h_c_poly[of _ _ "[:0,1:]"])
  qed
  from this obtain g where g: "?lhs = ?rhs * g" using dvdE by blast
  have degree_lhs_card: "degree ?lhs = CARD('a)"
  proof -
    have "degree (monom (1::'a mod_ring) 1) = 1" by (simp add: degree_monom_eq)
    moreover have d_c: "degree (monom (1::'a mod_ring) CARD('a)) = CARD('a)"
      by (simp add: degree_monom_eq)
    ultimately have "degree (monom (1::'a mod_ring) 1) < degree (monom (1::'a mod_ring) CARD('a))"
      using prime_card unfolding prime_nat_iff by auto
    hence "degree ?lhs = degree (monom (1::'a mod_ring) CARD('a))"
      by (rule degree_minus_eq_right)
    thus ?thesis unfolding d_c .
  qed
  have degree_rhs_card: "degree ?rhs = CARD('a)"
  proof -
    have "degree (prod ?f UNIV) = sum (degree \<circ> ?f) UNIV
      \<and> coeff (prod ?f UNIV) (sum (degree \<circ> ?f) UNIV) = 1"
      by (rule degree_prod_sum_monic, auto)
    moreover have "sum (degree \<circ> ?f) UNIV = CARD('a)" by auto
    ultimately show ?thesis by presburger
  qed
  have monic_lhs: "monic ?lhs" using degree_lhs_card by auto
  have monic_rhs: "monic ?rhs" by (rule monic_prod, simp)
  have degree_eq: "degree ?rhs = degree ?lhs" unfolding degree_lhs_card degree_rhs_card ..
  have g_not_0: "g \<noteq> 0" using g monic_lhs by auto
  have degree_g0: "degree g = 0"
  proof -
    have "degree (?rhs * g) = degree ?rhs + degree g"
      by (rule degree_monic_mult[OF monic_rhs g_not_0])
    thus ?thesis using degree_eq g by simp
  qed
  have monic_g: "monic g" using monic_factor g monic_lhs monic_rhs by auto
  have "g = 1" using monic_degree_0[OF monic_g] degree_g0 by simp
  thus ?thesis using g by auto
qed


(*
  Proof of equation 10 in the book by Knuth
  v(x)^p - v(x) = (v(x)-0)(v(x)-1)...(v(x)-(p-1))  (mod p)
*)


lemma poly_identity_mod_p:
  "v^(CARD('a)) - v = prod (\<lambda>x. v - [:x:]) (UNIV::'a mod_ring set)"
 proof -
  have id: "monom 1 1 \<circ>\<^sub>p v = v" "[:0, 1:] \<circ>\<^sub>p v = v" unfolding pcompose_def
    apply (auto)
    by (simp add: fold_coeffs_def)
  have id2: "monom 1 (CARD('a)) \<circ>\<^sub>p v = v ^ (CARD('a))" by (metis id(1) pcompose_hom.hom_power x_pow_n)
  show ?thesis using arg_cong[OF poly_monom_identity_mod_p, of "\<lambda> f. f \<circ>\<^sub>p v"]
    unfolding pcompose_hom.hom_minus pcompose_hom.hom_prod id pcompose_const id2 .
qed



lemma coprime_gcd:
  fixes h::"'a mod_ring poly"
  assumes "Rings.coprime (h-[:c1:]) (h-[:c2:])"
  shows "Rings.coprime (gcd f(h-[:c1:])) (gcd f (h-[:c2:]))"
  using assms coprime_divisors by blast


lemma divides_prod_gcd:
  fixes h::"'a mod_ring poly"
  assumes "\<forall>c1 c2. c1 \<in> A \<and> c2 \<in> A \<and> c1 \<noteq> c2\<longrightarrow> coprime (h-[:c1:]) (h-[:c2:])"
  shows "(\<Prod>c\<in>A. gcd f (h - [:c:])) dvd f"
proof -
  have finite_A: "finite A" using finite[of A] .
  thus ?thesis using assms
  proof (induct A)
    case (insert x A)
    have "(\<Prod>c\<in>insert x A. gcd f (h - [:c:])) =  (gcd f (h - [:x:])) * (\<Prod>c\<in> A. gcd f (h - [:c:]))"
      by (simp add: insert.hyps(2))
    also have "... dvd f"
    proof (rule divides_mult)
      show "gcd f (h - [:x:]) dvd f" by simp
      show "(\<Prod>c\<in>A. gcd f (h - [:c:])) dvd f" using insert.hyps(3) insert.prems by auto
      show "Rings.coprime (gcd f (h - [:x:])) (\<Prod>c\<in>A. gcd f (h - [:c:]))"
        by (rule prod_coprime_right)
          (metis Berlekamp_Type_Based.coprime_h_c_poly coprime_gcd coprime_iff_coprime insert.hyps(2))
    qed
    finally show ?case .
   qed auto
qed

lemma monic_prod_gcd:
assumes f: "finite A" and f0: "(f :: 'b :: {field_gcd} poly) \<noteq> 0"
shows "monic (\<Prod>c\<in>A. gcd f (h - [:c:]))"
using f
proof (induct A)
  case (insert x A)
  have rw: "(\<Prod>c\<in>insert x A. gcd f (h - [:c:]))
    = (gcd f (h - [:x:])) * (\<Prod>c\<in> A. gcd f (h - [:c:]))"
   by (simp add: insert.hyps)
  show ?case
  proof (unfold rw, rule monic_mult)
    show "monic (gcd f (h - [:x:]))"
      using poly_gcd_monic[of f] f0
      using insert.prems insert_iff by blast
    show "monic (\<Prod>c\<in>A. gcd f (h - [:c:]))"
      using insert.hyps(3) insert.prems by blast
  qed
qed auto

lemma coprime_not_unit_not_dvd:
fixes a::"'b::semiring_gcd"
assumes "a dvd b"
and "coprime b c"
and "\<not> is_unit a"
shows "\<not> a dvd c"
using assms coprime_divisors coprime_id_is_unit by fastforce

lemma divides_prod2:
  fixes A::"'b::semiring_gcd set"
  assumes f: "finite A"
  and "\<forall>a\<in>A. a dvd c"
  and "\<forall>a1 a2. a1 \<in> A \<and> a2 \<in> A \<and> a1 \<noteq> a2 \<longrightarrow> coprime a1 a2"
  shows "\<Prod>A dvd c"
using assms
proof (induct A)
  case (insert x A)
  have "\<Prod>(insert x A) = x * \<Prod>A" by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... dvd c"
  proof (rule divides_mult)
    show "x dvd c" by (simp add: insert.prems)
    show "\<Prod>A dvd c" using insert by auto
    from insert show "Rings.coprime x (\<Prod>A)"
      by (auto intro: prod_coprime_right)
  qed
  finally show ?case .
qed auto


lemma coprime_polynomial_factorization:
  fixes a1 :: "'b :: {field_gcd} poly"
  assumes  irr: "as \<subseteq> {q. irreducible q \<and> monic q}"
  and "finite as" and a1: "a1 \<in> as" and a2: "a2 \<in> as" and a1_not_a2: "a1 \<noteq> a2"
  shows "coprime a1 a2"
proof (rule ccontr)
  assume not_coprime: "\<not> coprime a1 a2"
  let ?b= "gcd a1 a2"
  have b_dvd_a1: "?b dvd a1" and b_dvd_a2: "?b dvd a2" by simp+
  have irr_a1: "irreducible a1" using a1 irr by blast
  have irr_a2: "irreducible a2" using a2 irr by blast
  have a2_not0: "a2 \<noteq> 0" using a2 irr by auto
  have degree_a1: "degree a1 \<noteq> 0" using irr_a1 by auto
  have degree_a2: "degree a2 \<noteq> 0" using irr_a2 by auto
  have not_a2_dvd_a1: "\<not> a2 dvd a1"
  proof (rule ccontr, simp)
    assume a2_dvd_a1: "a2 dvd a1"
    from this obtain k where k: "a1 = a2 * k" unfolding dvd_def by auto
    have k_not0: "k \<noteq> 0" using degree_a1 k by auto
    show False
    proof (cases "degree a2 = degree a1")
      case False
      have "degree a2 < degree a1"
        using False a2_dvd_a1 degree_a1 divides_degree
        by fastforce
      hence "\<not> irreducible a1"
        using degree_a2 a2_dvd_a1 degree_a2
        by (metis degree_a1 irreducible\<^sub>dD(2) irreducible\<^sub>d_multD irreducible_connect_field k neq0_conv)
      thus False using irr_a1 by contradiction
    next
      case True
      have "degree a1 = degree a2 + degree k"
        unfolding k using degree_mult_eq[OF a2_not0 k_not0] by simp
      hence "degree k = 0" using True by simp
      hence "k = 1" using monic_factor a1 a2 irr k monic_degree_0 by auto
      hence "a1 = a2" using k by simp
      thus False using a1_not_a2 by contradiction
    qed
  qed
  have b_not0: "?b \<noteq> 0" by (simp add: a2_not0)
  have degree_b: "degree ?b > 0"
    using not_coprime[simplified] b_not0 is_unit_gcd is_unit_iff_degree by blast
  have "degree ?b < degree a2"
    by (meson b_dvd_a1 b_dvd_a2 irreducibleD' dvd_trans gcd_dvd_1 irr_a2 not_a2_dvd_a1 not_coprime)
  hence "\<not> irreducible\<^sub>d a2" using degree_a2 b_dvd_a2 degree_b
    by (metis degree_smult_eq irreducible\<^sub>d_dvd_smult less_not_refl3)
  thus False using irr_a2 by auto
qed

(*
  Proof of equation 14 in the book by Knuth
*)
theorem Berlekamp_gcd_step:
fixes f::"'a mod_ring poly" and h::"'a mod_ring poly"
assumes hq_mod_f: "[h^(CARD('a)) = h] (mod f)" and monic_f: "monic f" and sf_f: "square_free f"
shows "f = prod (\<lambda>c. gcd f (h - [:c:])) (UNIV::'a mod_ring set)"  (is "?lhs = ?rhs")
proof (cases "f=0")
  case True
  thus ?thesis using coeff_0 monic_f zero_neq_one by auto
  next
  case False note f_not_0 = False
  show ?thesis
  proof (rule poly_dvd_antisym)
    show "?rhs dvd f"
      using coprime_h_c_poly by (intro divides_prod_gcd, auto)
    have "monic ?rhs" by (rule monic_prod_gcd[OF _ f_not_0], simp)
    thus "coeff f (degree f) = coeff ?rhs (degree ?rhs)"
      using monic_f by auto
    next
    show "f dvd ?rhs"
    proof -
      let ?p = "CARD('a)"
      obtain P  where finite_P: "finite P"
      and f_desc_square_free: "f = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
        using monic_square_free_irreducible_factorization[OF monic_f sf_f] by auto
      have f_dvd_hqh: "f dvd (h^?p - h)" using hq_mod_f unfolding cong_def
        using mod_eq_dvd_iff_poly by blast
      also have hq_h_rw: "... = prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)"
        by (rule poly_identity_mod_p)
      finally have f_dvd_hc: "f dvd prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)" by simp
      have "f = \<Prod>P" using f_desc_square_free by simp
      also have "... dvd ?rhs"
      proof (rule divides_prod2[OF finite_P])
        show "\<forall>a1 a2. a1 \<in> P \<and> a2 \<in> P \<and> a1 \<noteq> a2 \<longrightarrow> coprime a1 a2"
          using coprime_polynomial_factorization[OF P finite_P] by simp
        show "\<forall>a\<in>P. a dvd (\<Prod>c\<in>UNIV. gcd f (h - [:c:]))"
        proof
          fix fi assume fi_P: "fi \<in> P"
          show "fi dvd ?rhs"
          proof (rule dvd_prod, auto)
            show "fi dvd f" using f_desc_square_free fi_P
             using dvd_prod_eqI finite_P by blast
            hence "fi dvd (h^?p - h)" using dvd_trans f_dvd_hqh by auto
            also have "... = prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)"
              unfolding hq_h_rw by simp
            finally have fi_dvd_prod_hc: "fi dvd prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)" .
            have irr_fi: "irreducible (fi)" using fi_P P by blast
            have fi_not_unit: "\<not> is_unit fi" using irr_fi by (simp add: irreducible\<^sub>dD(1) poly_dvd_1)
            have fi_dvd_hc: "\<exists>c\<in>UNIV::'a mod_ring set. fi dvd (h-[:c:])"
              by (rule irreducible_dvd_prod[OF _ fi_dvd_prod_hc], simp add: irr_fi)
            thus "\<exists>c. fi dvd h - [:c:]" by simp
          qed
        qed
      qed
      finally show "f dvd ?rhs" .
    qed
  qed
qed


(******* Implementation of Berlekamp's algorithm (type-based version) *******)
subsection \<open>Definitions\<close>

definition berlekamp_mat :: "'a mod_ring poly \<Rightarrow> 'a mod_ring mat" where
  "berlekamp_mat u = (let n = degree u;
    mul_p = power_poly_f_mod u [:0,1:] (CARD('a));
    xks = power_polys mul_p u 1 n
   in
    mat_of_rows_list n (map (\<lambda> cs. let coeffs_cs = (coeffs cs);
                                        k = n - length (coeffs cs)
                                   in (coeffs cs) @ replicate k 0) xks))"


definition berlekamp_resulting_mat :: "('a mod_ring) poly \<Rightarrow> 'a mod_ring mat" where
"berlekamp_resulting_mat u = (let Q = berlekamp_mat u;
    n = dim_row Q;
    QI = mat n n (\<lambda> (i,j). if i = j then Q $$ (i,j) - 1 else Q $$ (i,j))
    in (gauss_jordan_single (transpose_mat QI)))"

definition berlekamp_basis :: "'a mod_ring poly \<Rightarrow> 'a mod_ring poly list" where
  "berlekamp_basis u = (map (Poly o list_of_vec) (find_base_vectors (berlekamp_resulting_mat u)))"

lemma berlekamp_basis_code[code]: "berlekamp_basis u =
  (map (poly_of_list o list_of_vec) (find_base_vectors (berlekamp_resulting_mat u)))"
  unfolding berlekamp_basis_def poly_of_list_def ..

primrec berlekamp_factorization_main :: "nat \<Rightarrow> 'a mod_ring poly list \<Rightarrow> 'a mod_ring poly list \<Rightarrow> nat \<Rightarrow> 'a mod_ring poly list" where
  "berlekamp_factorization_main i divs (v # vs) n = (if v = 1 then berlekamp_factorization_main i divs vs n else
    if length divs = n then divs else
    let facts = [ w . u \<leftarrow> divs, s \<leftarrow> [0 ..< CARD('a)], w \<leftarrow> [gcd u (v - [:of_int s:])], w \<noteq> 1];
      (lin,nonlin) = List.partition (\<lambda> q. degree q = i) facts
      in lin @ berlekamp_factorization_main i nonlin vs (n - length lin))"
  | "berlekamp_factorization_main i divs [] n = divs"
  
definition berlekamp_monic_factorization :: "nat \<Rightarrow> 'a mod_ring poly \<Rightarrow> 'a mod_ring poly list" where
  "berlekamp_monic_factorization d f = (let
     vs = berlekamp_basis f;
     n = length vs;
     fs = berlekamp_factorization_main d [f] vs n
    in fs)"

subsection \<open>Properties\<close>

lemma power_polys_works:
fixes u::"'b::unique_euclidean_semiring"
assumes i: "i < n" and c: "curr_p = curr_p mod u" (*Equivalent to degree curr_p < degree u*)
shows "power_polys mult_p u curr_p n ! i = curr_p * mult_p ^ i mod u"
using i c
proof (induct n arbitrary: curr_p i)
  case 0 thus ?case by simp
next
  case (Suc n)
  have p_rw: "power_polys mult_p u curr_p (Suc n) ! i
      = (curr_p # power_polys mult_p u (curr_p * mult_p mod u) n) ! i"
    by simp
  show ?case
  proof (cases "i=0")
    case True
    show ?thesis using Suc.prems unfolding p_rw True by auto
  next
    case False note i_not_0 = False
    show ?thesis
    proof (cases "i < n")
      case True note i_less_n = True
      have "power_polys mult_p u curr_p (Suc n) ! i = power_polys mult_p u (curr_p * mult_p mod u) n ! (i - 1)"
        unfolding p_rw using nth_Cons_pos False by auto
      also have "... = (curr_p * mult_p mod u) * mult_p ^ (i-1) mod u"
        by (rule Suc.hyps) (auto simp add: i_less_n less_imp_diff_less)
      also have "... = curr_p * mult_p ^ i mod u"
        using False by (cases i) (simp_all add: algebra_simps mod_simps)
      finally show ?thesis .
    next
      case False
      hence i_n: "i = n" using Suc.prems by auto
      have "power_polys mult_p u curr_p (Suc n) ! i = power_polys mult_p u (curr_p * mult_p mod u) n ! (n - 1)"
          unfolding p_rw using nth_Cons_pos i_n i_not_0 by auto
      also have "... = (curr_p * mult_p mod u) * mult_p ^ (n-1) mod u"
      proof (rule Suc.hyps)
        show "n - 1 < n" using i_n i_not_0 by linarith
        show "curr_p * mult_p mod u = curr_p * mult_p mod u mod u" by simp
      qed
      also have "... = curr_p * mult_p ^ i mod u"
        using i_n [symmetric] i_not_0 by (cases i) (simp_all add: algebra_simps mod_simps)
      finally show ?thesis .
    qed
  qed
qed


lemma length_power_polys[simp]: "length (power_polys mult_p u curr_p n) = n"
  by (induct n arbitrary: curr_p, auto)


(*
  Equation 12
*)

lemma Poly_berlekamp_mat:
assumes k: "k < degree u"
shows "Poly (list_of_vec (row (berlekamp_mat u) k)) = [:0,1:]^(CARD('a) * k) mod u"
proof -
  let ?map ="(map (\<lambda>cs. coeffs cs @ replicate (degree u - length (coeffs cs)) 0)
              (power_polys (power_poly_f_mod u [:0, 1:] (nat (int CARD('a)))) u 1 (degree u)))"
  have "row (berlekamp_mat u) k = row (mat_of_rows_list (degree u) ?map) k"
    by (simp add: berlekamp_mat_def Let_def)
  also have "... = vec_of_list (?map ! k)"
  proof-
    {
      fix i assume i: "i < degree u"
      let ?c= "power_polys (power_poly_f_mod u [:0, 1:] CARD('a)) u 1 (degree u) ! i"
      let ?coeffs_c="(coeffs ?c)"
      have "?c = 1*([:0, 1:] ^ CARD('a) mod u)^i mod u"
      proof (unfold power_poly_f_mod_def, rule power_polys_works[OF i])
        show "1 = 1 mod u" using k mod_poly_less by force
      qed
      also have "... = [:0, 1:] ^ (CARD('a) * i) mod u" by (simp add: power_mod power_mult)
      finally have c_rw: "?c = [:0, 1:] ^ (CARD('a) * i) mod u" .
      have "length ?coeffs_c \<le> degree u"
      proof -
        show ?thesis
        proof (cases "?c = 0")
          case True thus ?thesis by auto
          next
          case False
          have "length ?coeffs_c = degree (?c) + 1" by (rule length_coeffs[OF False])
          also have "... = degree ([:0, 1:] ^ (CARD('a) * i) mod u) + 1" using c_rw by simp
          also have "... \<le> degree u"
            by (metis One_nat_def add.right_neutral add_Suc_right c_rw calculation coeffs_def degree_0
              degree_mod_less discrete gr_implies_not0 k list.size(3) one_neq_zero)
          finally show ?thesis .
        qed
      qed
      then have "length ?coeffs_c + (degree u - length ?coeffs_c) = degree u" by auto
    }
    with k show ?thesis by (intro row_mat_of_rows_list, auto)
  qed
  finally have row_rw: "row (berlekamp_mat u) k = vec_of_list (?map ! k)" .
  have "Poly (list_of_vec (row (berlekamp_mat u) k)) = Poly (list_of_vec (vec_of_list (?map ! k)))"
    unfolding row_rw ..
  also have "... = Poly (?map ! k)" by simp
  also have "... = [:0,1:]^(CARD('a) * k) mod u"
  proof -
    let ?cs = "(power_polys (power_poly_f_mod u [:0, 1:] (nat (int CARD('a)))) u 1 (degree u)) ! k"
    let ?c = "coeffs ?cs @ replicate (degree u - length (coeffs ?cs)) 0"
    have map_k_c: "?map ! k = ?c" by (rule nth_map, simp add: k)
    have "(Poly (?map ! k)) = Poly (coeffs ?cs)" unfolding map_k_c Poly_append_replicate_0 ..
    also have "... = ?cs" by simp
    also have "... = power_polys ([:0, 1:] ^ CARD('a) mod u) u 1 (degree u) ! k"
      by (simp add: power_poly_f_mod_def)
    also have "... = 1* ([:0,1:]^(CARD('a)) mod u) ^ k mod u"
    proof (rule power_polys_works[OF k])
      show "1 = 1 mod u" using k mod_poly_less by force
    qed
    also have "... = ([:0,1:]^(CARD('a)) mod u) ^ k mod u" by auto
    also have "... = [:0,1:]^(CARD('a) * k) mod u" by (simp add: power_mod power_mult)
    finally show ?thesis .
  qed
    finally show ?thesis .
qed

corollary Poly_berlekamp_cong_mat:
assumes k: "k < degree u"
shows "[Poly (list_of_vec (row (berlekamp_mat u) k)) = [:0,1:]^(CARD('a) * k)] (mod u)"
using Poly_berlekamp_mat[OF k] unfolding cong_def by auto

lemma mat_of_rows_list_dim[simp]:
  "mat_of_rows_list n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows_list n vs) = length vs"
  "dim_col (mat_of_rows_list n vs) = n"
  unfolding mat_of_rows_list_def by auto

lemma berlekamp_mat_closed[simp]:
  "berlekamp_mat u \<in> carrier_mat (degree u) (degree u)"
  "dim_row (berlekamp_mat u) = degree u"
  "dim_col (berlekamp_mat u) = degree u"
 unfolding carrier_mat_def berlekamp_mat_def Let_def by auto


lemma vec_of_list_coeffs_nth:
assumes i: "i \<in> {..degree h}" and h_not0: "h \<noteq> 0"
shows "vec_of_list (coeffs h) $ i = coeff h i"
proof -
  have "vec_of_list (map (coeff h) [0..<degree h] @ [coeff h (degree h)]) $ i = coeff h i"
      using i
      by (transfer', auto simp add: mk_vec_def)
         (metis (no_types, lifting) Cons_eq_append_conv coeffs_def coeffs_nth degree_0
         diff_zero length_upt less_eq_nat.simps(1) list.simps(8) list.simps(9) map_append
         nth_Cons_0 upt_Suc upt_eq_Nil_conv)
  thus "vec_of_list (coeffs h) $ i = coeff h i"
    using i h_not0
    unfolding coeffs_def by simp
qed



lemma poly_mod_sum:
  fixes x y z :: "'b::field poly"
  assumes f: "finite A"
  shows "sum f A mod z = sum (\<lambda>i. f i mod z) A"
using f
by (induct, auto simp add: poly_mod_add_left)


lemma prime_not_dvd_fact:
assumes kn: "k < n" and prime_n: "prime n"
shows "\<not> n dvd fact k"
using kn
proof (induct k)
  case 0
  thus ?case using prime_n unfolding prime_nat_iff by auto
next
  case (Suc k)
  show ?case
  proof (rule ccontr, unfold not_not)
    assume "n dvd fact (Suc k)"
    also have "... = Suc k * \<Prod>{1..k}" unfolding fact_Suc unfolding fact_prod by simp
    finally have "n dvd Suc k * \<Prod>{1..k}" .
    hence "n dvd Suc k \<or> n dvd \<Prod>{1..k}" using prime_dvd_mult_eq_nat[OF prime_n] by blast
    moreover have  "\<not> n dvd Suc k" by (simp add: Suc.prems(1) nat_dvd_not_less)
    moreover hence "\<not> n dvd \<Prod>{1..k}" using Suc.hyps Suc.prems
      using Suc_lessD fact_prod[of k] by (metis of_nat_id)
    ultimately show False by simp
  qed
qed


lemma dvd_choose_prime:
assumes kn: "k < n" and k: "k \<noteq> 0" and n: "n \<noteq> 0" and prime_n: "prime n"
shows "n dvd (n choose k)"
proof -
  have "n dvd (fact n)" by (simp add: fact_num_eq_if n)
  moreover have "\<not> n dvd (fact k * fact (n-k))"
  proof (rule ccontr, simp)
    assume "n dvd fact k * fact (n - k)"
    hence "n dvd fact k \<or> n dvd fact (n - k)" using prime_dvd_mult_eq_nat[OF prime_n] by simp
    moreover have "\<not> n dvd (fact k)" by (rule prime_not_dvd_fact[OF kn prime_n])
    moreover have "\<not> n dvd fact (n - k)" using  prime_not_dvd_fact[OF _ prime_n] kn k by simp
    ultimately show False by simp
  qed
  moreover have "(fact n::nat) = fact k * fact (n-k) * (n choose k)"
    using binomial_fact_lemma kn by auto
  ultimately show ?thesis using prime_n
    by (auto simp add: prime_dvd_mult_iff)
qed



lemma add_power_poly_mod_ring:
fixes x :: "'a mod_ring poly"
shows "(x + y) ^ CARD('a) = x ^ CARD('a) + y ^ CARD('a)"
proof -
  let ?A="{0..CARD('a)}"
  let ?f="\<lambda>k. of_nat (CARD('a) choose k) * x ^ k * y ^ (CARD('a) - k)"
  have A_rw: "?A = insert CARD('a) (insert 0 (?A - {0} - {CARD('a)}))"
    by fastforce
  have sum0: "sum ?f (?A - {0} - {CARD('a)}) = 0"
  proof (rule sum.neutral, rule)
    fix xa assume xa: "xa \<in> {0..CARD('a)} - {0} - {CARD('a)}"
    have card_dvd_choose: "CARD('a) dvd  (CARD('a) choose xa)"
    proof (rule dvd_choose_prime)
      show "xa < CARD('a)" using xa by simp
      show "xa \<noteq> 0" using xa by simp
      show "CARD('a) \<noteq> 0" by simp
      show "prime CARD('a)" by (rule prime_card)
    qed
    hence rw0: "of_int (CARD('a) choose xa) = (0 :: 'a mod_ring)"
      by transfer simp
    have "of_nat (CARD('a) choose xa) = [:of_int (CARD('a) choose xa) :: 'a mod_ring:]"
      by (simp add: of_nat_poly)
    also have "... = [:0:]" using rw0 by simp
    finally show "of_nat (CARD('a) choose xa) * x ^ xa * y ^ (CARD('a) - xa) = 0" by auto
  qed
  have "(x + y)^CARD('a)
    = (\<Sum>k = 0..CARD('a). of_nat (CARD('a) choose k) * x ^ k * y ^ (CARD('a) - k))"
    unfolding binomial_ring by (rule sum.cong, auto)
  also have "... = sum ?f (insert CARD('a) (insert 0 (?A - {0} - {CARD('a)})))"
    using A_rw by simp
  also have "... = ?f 0 + ?f CARD('a) + sum ?f (?A - {0} - {CARD('a)})" by auto
  also have "... = x^CARD('a) + y^CARD('a)" unfolding sum0 by auto
  finally show ?thesis .
qed


lemma power_poly_sum_mod_ring:
fixes f :: "'b \<Rightarrow> 'a mod_ring poly"
assumes f: "finite A"
shows "(sum f A) ^ CARD('a) = sum (\<lambda>i. (f i) ^ CARD('a)) A"
using f by (induct, auto simp add: add_power_poly_mod_ring)


lemma poly_power_card_as_sum_of_monoms:
  fixes h :: "'a mod_ring poly"
  shows "h ^ CARD('a) = (\<Sum>i\<le>degree h. monom (coeff h i) (CARD('a)*i))"
proof -
  have "h ^ CARD('a) = (\<Sum>i\<le>degree h. monom (coeff h i) i) ^ CARD('a)"
    by (simp add: poly_as_sum_of_monoms)
  also have "... = (\<Sum>i\<le>degree h. (monom (coeff h i) i) ^ CARD('a))"
    by (simp add: power_poly_sum_mod_ring)
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) (CARD('a)*i))"
  proof (rule sum.cong, rule)
    fix x assume x: "x \<in> {..degree h}"
    show "monom (coeff h x) x ^ CARD('a) = monom (coeff h x) (CARD('a) * x)"
      by (unfold poly_eq_iff, auto simp add: monom_power)
  qed
  finally show ?thesis .
qed


lemma degree_Poly_berlekamp_le:
assumes i: "i < degree u"
shows "degree (Poly (list_of_vec (row (berlekamp_mat u) i))) < degree u"
by (metis Poly_berlekamp_mat degree_0 degree_mod_less gr_implies_not0 i linorder_neqE_nat)


(*
  Equation 12: alternative statement.
*)

lemma monom_card_pow_mod_sum_berlekamp:
assumes i: "i < degree u"
shows "monom 1 (CARD('a) * i) mod u = (\<Sum>j<degree u. monom ((berlekamp_mat u) $$ (i,j)) j)"
proof -
  let ?p = "Poly (list_of_vec (row (berlekamp_mat u) i))"
  have degree_not_0: "degree u \<noteq> 0" using i by simp
  hence set_rw: "{..degree u - 1} = {..<degree u}" by auto
  have degree_le: "degree ?p < degree u"
    by (rule degree_Poly_berlekamp_le[OF i])
  hence degree_le2: "degree ?p \<le> degree u - 1" by auto
  have "monom 1 (CARD('a) * i) mod u = [:0, 1:] ^ (CARD('a) * i) mod u"
    using x_as_monom x_pow_n by metis
  also have "... = ?p"
    unfolding Poly_berlekamp_mat[OF i] by simp
  also have "... = (\<Sum>i\<le>degree u - 1. monom (coeff ?p i) i)"
        using degree_le2 poly_as_sum_of_monoms' by fastforce
  also have "... = (\<Sum>i<degree u. monom (coeff ?p i) i)" using set_rw by auto
  also have "... = (\<Sum>j<degree u. monom ((berlekamp_mat u) $$ (i,j)) j)"
  proof (rule sum.cong, rule)
    fix x assume x: "x \<in> {..<degree u}"
    have "coeff ?p x = berlekamp_mat u $$ (i, x)"
    proof (rule coeff_Poly_list_of_vec_nth)
      show "x < dim_col (berlekamp_mat u)" using x by auto
    qed
    thus "monom (coeff ?p x) x = monom (berlekamp_mat u $$ (i, x)) x"
      by (simp add: poly_eq_iff)
  qed
  finally show ?thesis .
qed



lemma col_scalar_prod_as_sum:
assumes "dim_vec v = dim_row A"
shows "col A j \<bullet> v = (\<Sum>i = 0..<dim_vec v. A $$ (i,j) * v $ i)"
  using assms
  unfolding col_def scalar_prod_def
  by transfer' (rule sum.cong, transfer', auto simp add: mk_vec_def mk_mat_def )

lemma row_transpose_scalar_prod_as_sum:
assumes j: "j < dim_col A" and dim_v: "dim_vec v = dim_row A"
shows "row (transpose_mat A) j \<bullet> v = (\<Sum>i = 0..<dim_vec v. A $$ (i,j) * v $ i)"
proof -
  have "row (transpose_mat A) j \<bullet> v = col A j \<bullet> v" using j row_transpose by auto
  also have "... = (\<Sum>i = 0..<dim_vec v. A $$ (i,j) * v $ i)"
    by (rule col_scalar_prod_as_sum[OF dim_v])
  finally show ?thesis .
qed


lemma poly_as_sum_eq_monoms:
assumes ss_eq: "(\<Sum>i<n. monom (f i) i) = (\<Sum>i<n. monom (g i) i)"
and a_less_n: "a<n"
shows "f a = g a"
proof -
  let ?f="\<lambda>i. if i = a then f i else 0"
  let ?g="\<lambda>i. if i = a then g i else 0"
  have sum_f_0: "sum ?f ({..<n} - {a}) = 0" by (rule sum.neutral, auto)
  have "coeff (\<Sum>i<n. monom (f i) i) a = coeff (\<Sum>i<n. monom (g i) i) a"
    using ss_eq unfolding poly_eq_iff by simp
  hence "(\<Sum>i<n. coeff (monom (f i) i) a) = (\<Sum>i<n. coeff (monom (g i) i) a)"
    by (simp add: coeff_sum)
  hence 1: "(\<Sum>i<n. if i = a then f i else 0) = (\<Sum>i<n. if i = a then g i else 0)"
    unfolding coeff_monom by auto
  have set_rw: "{..<n} = (insert a ({..<n} - {a}))" using a_less_n by auto
  have "(\<Sum>i<n. if i = a then f i else 0) = sum ?f (insert a ({..<n} - {a}))"
    using set_rw by auto
  also have "... = ?f a + sum ?f ({..<n} - {a})"
    by (simp add: sum.insert_remove)
  also have "... = ?f a" using sum_f_0 by simp
  finally have 2: "(\<Sum>i<n. if i = a then f i else 0) = ?f a" .
  have "sum ?g {..<n} = sum ?g (insert a ({..<n} - {a}))"
    using set_rw by auto
  also have "... = ?g a + sum ?g ({..<n} - {a})"
    by (simp add: sum.insert_remove)
  also have "... = ?g a" using sum_f_0 by simp
  finally have 3: "(\<Sum>i<n. if i = a then g i else 0) = ?g a" .
  show ?thesis using 1 2 3 by auto
qed



lemma dim_vec_of_list_h:
assumes "degree h < degree u"
shows "dim_vec (vec_of_list ((coeffs h) @ replicate (degree u - length (coeffs h)) 0)) = degree u"
proof -
  have "length (coeffs h) \<le> degree u"
    by (metis Suc_leI assms coeffs_0_eq_Nil degree_0 length_coeffs_degree
        list.size(3) not_le_imp_less order.asym)
  thus ?thesis by simp
qed




lemma vec_of_list_coeffs_nth':
assumes i: "i \<in> {..degree h}" and h_not0: "h \<noteq> 0"
assumes "degree h < degree u"
shows "vec_of_list ((coeffs h) @ replicate (degree u - length (coeffs h)) 0) $ i = coeff h i"
using assms
by (transfer', auto simp add: mk_vec_def coeffs_nth length_coeffs_degree nth_append)


lemma vec_of_list_coeffs_replicate_nth_0:
assumes i: "i \<in> {..<degree u}"
shows "vec_of_list (coeffs 0 @ replicate (degree u - length (coeffs 0)) 0) $ i = coeff 0 i"
using assms
by (transfer', auto simp add: mk_vec_def)


lemma vec_of_list_coeffs_replicate_nth:
assumes i: "i \<in> {..<degree u}"
assumes "degree h < degree u"
shows "vec_of_list ((coeffs h) @ replicate (degree u - length (coeffs h)) 0) $ i = coeff h i"
proof (cases "h = 0")
  case True
  thus ?thesis using vec_of_list_coeffs_replicate_nth_0 i by auto
next
  case False note h_not0 = False
  show ?thesis
  proof (cases "i \<in>{..degree h}")
    case True thus ?thesis using assms vec_of_list_coeffs_nth' h_not0 by simp
  next
    case False
    have c0: "coeff h i = 0" using False le_degree by auto
    thus ?thesis
      using assms False h_not0
      by (transfer', auto simp add: mk_vec_def length_coeffs_degree nth_append c0)
  qed
qed


(*
  Equation 13
*)

lemma equation_13:
  fixes u h
  defines H: "H \<equiv> vec_of_list ((coeffs h) @ replicate (degree u - length (coeffs h)) 0)"
  assumes deg_le: "degree h < degree u" (*Mandatory from equation 8*)
  shows "[h^CARD('a) = h] (mod u) \<longleftrightarrow> (transpose_mat (berlekamp_mat u)) *\<^sub>v H = H"
  (is "?lhs = ?rhs")
proof -
  have f: "finite {..degree u}" by auto
  have [simp]: "dim_vec H = degree u" unfolding H using dim_vec_of_list_h deg_le by simp
  let ?B = "(berlekamp_mat u)"
  let ?f = "\<lambda>i. (transpose_mat ?B *\<^sub>v H) $ i"
  show ?thesis
  proof
  assume rhs: ?rhs
  have dimv_h_dimr_B: "dim_vec H = dim_row ?B"
    by (metis berlekamp_mat_closed(2) berlekamp_mat_closed(3)
        dim_mult_mat_vec index_transpose_mat(2) rhs)
  have degree_h_less_dim_H: "degree h < dim_vec H" by (auto simp add: deg_le)
  have set_rw: "{..degree u - 1} = {..<degree u}" using deg_le by auto
  have "degree h \<le> degree u - 1" using deg_le by simp
  hence "h = (\<Sum>j\<le>degree u - 1. monom (coeff h j) j)" using poly_as_sum_of_monoms' by fastforce
  also have "... = (\<Sum>j<degree u. monom (coeff h j) j)" using set_rw by simp
    also have "... = (\<Sum>j<degree u. monom (?f j) j)"
    proof (rule sum.cong, rule+)
      fix j assume i: "j \<in> {..<degree u}"
      have "(coeff h j) = ?f j"
        using rhs vec_of_list_coeffs_replicate_nth[OF i deg_le]
        unfolding H by presburger
      thus "monom (coeff h j) j = monom (?f j) j"
        by simp
    qed
    also have "... = (\<Sum>j<degree u. monom (row (transpose_mat ?B) j \<bullet> H) j)"
      by (rule sum.cong, auto)
    also have "... = (\<Sum>j<degree u. monom (\<Sum>i = 0..<dim_vec H. ?B $$ (i,j) * H $ i) j)"
    proof (rule sum.cong, rule)
      fix x assume x: "x \<in> {..<degree u}"
      show "monom (row (transpose_mat ?B) x \<bullet> H) x =
      monom (\<Sum>i = 0..<dim_vec H. ?B $$ (i, x) * H $ i) x"
      proof (unfold monom_eq_iff, rule row_transpose_scalar_prod_as_sum[OF _ dimv_h_dimr_B])
        show "x < dim_col ?B" using x deg_le by auto
      qed
    qed
    also have "... = (\<Sum>j<degree u. \<Sum>i = 0..<dim_vec H. monom (?B $$ (i,j) * H $ i) j)"
      by (auto simp add: monom_sum)
    also have "... = (\<Sum>i = 0..<dim_vec H. \<Sum>j<degree u. monom (?B $$ (i,j) * H $ i) j)"
      by (rule sum.swap)
    also have "... = (\<Sum>i = 0..<dim_vec H. \<Sum>j<degree u.  monom (H $ i) 0 * monom (?B $$ (i,j)) j)"
    proof (rule sum.cong, rule, rule sum.cong, rule)
       fix x xa
       show "monom (?B $$ (x, xa) * H $ x) xa = monom (H $ x) 0 * monom (?B $$ (x, xa)) xa"
        by (simp add: mult_monom)
    qed
    also have "... = (\<Sum>i = 0..<dim_vec H. (monom (H $ i) 0) * (\<Sum>j<degree u. monom (?B $$ (i,j)) j))"
      by (rule sum.cong, auto simp: sum_distrib_left)
    also have "... = (\<Sum>i = 0..<dim_vec H. (monom (H $ i) 0) * (monom 1 (CARD('a) * i) mod u))"
    proof (rule sum.cong, rule)
      fix x assume x: "x \<in> {0..<dim_vec H}"
      have "(\<Sum>j<degree u. monom (?B $$ (x, j)) j) = (monom 1 (CARD('a) * x) mod u)"
      proof (rule monom_card_pow_mod_sum_berlekamp[symmetric])
        show "x < degree u" using x dimv_h_dimr_B by auto
      qed
      thus "monom (H $ x) 0 * (\<Sum>j<degree u. monom (?B $$ (x, j)) j) =
         monom (H $ x) 0 * (monom 1 (CARD('a) * x) mod u)" by presburger
    qed
    also have "... =  (\<Sum>i = 0..<dim_vec H. monom (H $ i) (CARD('a) * i) mod u)"
    proof (rule sum.cong, rule)
      fix x
      have h_rw: "monom (H $ x) 0 mod u = monom (H $ x) 0"
        by (metis deg_le degree_pCons_eq_if gr_implies_not_zero
           linorder_neqE_nat mod_poly_less monom_0)
      have "monom (H $ x) (CARD('a) * x) = monom (H $ x) 0 * monom 1 (CARD('a) * x)"
        unfolding mult_monom by simp
      also have "... = smult (H $ x) (monom 1 (CARD('a) * x))"
        by (simp add: monom_0)
      also have "... mod u =  Polynomial.smult (H $ x) (monom 1 (CARD('a) * x) mod u)"
        using mod_smult_left by auto
      also have "... = monom (H $ x) 0 * (monom 1 (CARD('a) * x) mod u)"
        by (simp add: monom_0)
      finally show "monom (H $ x) 0 * (monom 1 (CARD('a) * x) mod u)
        = monom (H $ x) (CARD('a) * x) mod u" ..
    qed
    also have "... = (\<Sum>i = 0..<dim_vec H. monom (H $ i) (CARD('a) * i)) mod u"
      by (simp add: poly_mod_sum)
    also have "... = (\<Sum>i = 0..<dim_vec H. monom (coeff h i) (CARD('a) * i)) mod u"
    proof (rule arg_cong[of _ _ "\<lambda>x. x  mod u"], rule sum.cong, rule)
       fix x assume x: "x \<in> {0..<dim_vec H}"
       have "H $ x = (coeff h x)"
       proof (unfold H, rule vec_of_list_coeffs_replicate_nth[OF _ deg_le])
          show "x \<in> {..<degree u}" using x by auto
       qed
       thus "monom (H $ x) (CARD('a) * x) = monom (coeff h x) (CARD('a) * x)"
        by simp
    qed
    also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) (CARD('a) * i)) mod u"
    proof (rule arg_cong[of _ _ "\<lambda>x. x mod u"])
      let ?f="\<lambda>i. monom (coeff h i) (CARD('a) * i)"
      have ss0: "(\<Sum>i = degree h + 1 ..< dim_vec H. ?f i) = 0"
        by (rule sum.neutral, simp add: coeff_eq_0)
      have set_rw: "{0..< dim_vec H} = {0..degree h} \<union> {degree h + 1 ..< dim_vec H}"
        using degree_h_less_dim_H by auto
      have "(\<Sum>i = 0..<dim_vec H. ?f i) = (\<Sum>i = 0..degree h. ?f i) + (\<Sum>i = degree h + 1 ..< dim_vec H. ?f i)"
        unfolding set_rw by (rule sum.union_disjoint, auto)
      also have "... = (\<Sum>i = 0..degree h. ?f i)" unfolding ss0 by auto
      finally show "(\<Sum>i = 0..<dim_vec H. ?f i) = (\<Sum>i\<le>degree h. ?f i)"
        by (simp add: atLeast0AtMost)
    qed
    also have "... = h^CARD('a) mod u"
      using poly_power_card_as_sum_of_monoms by auto
    finally show ?lhs
      unfolding cong_def
      using deg_le
      by (simp add: mod_poly_less)
next
  assume lhs: ?lhs
  have deg_le': "degree h \<le> degree u - 1" using deg_le by auto
  have set_rw: "{..<degree u} = {..degree u -1}" using deg_le by auto
  hence "(\<Sum>i<degree u. monom (coeff h i) i) = (\<Sum>i \<le> degree u - 1. monom (coeff h i) i)" by simp
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) i)"
    unfolding poly_as_sum_of_monoms
    using poly_as_sum_of_monoms' deg_le' by auto
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) i) mod u"
    by (simp add: deg_le mod_poly_less poly_as_sum_of_monoms)
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) (CARD('a)*i)) mod u"
     using lhs
     unfolding cong_def poly_as_sum_of_monoms poly_power_card_as_sum_of_monoms
     by auto
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) 0 * monom 1 (CARD('a)*i)) mod u"
    by (rule arg_cong[of _ _ "\<lambda>x. x mod u"], rule sum.cong, simp_all add: mult_monom)
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) 0 * monom 1 (CARD('a)*i) mod u)"
    by (simp add: poly_mod_sum)
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) 0 * (monom 1 (CARD('a)*i) mod u))"
  proof (rule sum.cong, rule)
    fix x assume x: "x \<in> {..degree h}"
    have h_rw: "monom (coeff h x) 0 mod u = monom (coeff h x) 0"
        by (metis deg_le degree_pCons_eq_if gr_implies_not_zero
           linorder_neqE_nat mod_poly_less monom_0)
      have "monom (coeff h x) 0 * monom 1 (CARD('a) * x) = smult (coeff h x) (monom 1 (CARD('a) * x))"
        by (simp add: monom_0)
      also have "... mod u =  Polynomial.smult (coeff h x) (monom 1 (CARD('a) * x) mod u)"
        using mod_smult_left by auto
      also have "... = monom (coeff h x) 0 * (monom 1 (CARD('a) * x) mod u)"
        by (simp add: monom_0)
    finally show "monom (coeff h x) 0 * monom 1 (CARD('a) * x) mod u
      = monom (coeff h x) 0 * (monom 1 (CARD('a) * x) mod u)" .
  qed
  also have "... = (\<Sum>i\<le>degree h. monom (coeff h i) 0 * (\<Sum>j<degree u. monom (?B $$ (i, j)) j))"
  proof (rule sum.cong, rule)
    fix x assume x: "x \<in> {..degree h}"
    have "(monom 1 (CARD('a) * x) mod u) = (\<Sum>j<degree u. monom (?B $$ (x, j)) j)"
    proof (rule monom_card_pow_mod_sum_berlekamp)
      show " x < degree u" using x deg_le by auto
    qed
    thus "monom (coeff h x) 0 * (monom 1 (CARD('a) * x) mod u) =
         monom (coeff h x) 0 * (\<Sum>j<degree u. monom (?B $$ (x, j)) j)" by simp
  qed
  also have "... = (\<Sum>i<degree u. monom (coeff h i) 0 * (\<Sum>j<degree u. monom (?B $$ (i, j)) j))"
  proof -
    let ?f="\<lambda>i. monom (coeff h i) 0 * (\<Sum>j<degree u. monom (?B $$ (i, j)) j)"
    have ss0: "(\<Sum>i=degree h+1 ..< degree u. ?f i) = 0"
      by (rule sum.neutral, simp add: coeff_eq_0)
    have set_rw: "{0..<degree u} = {0..degree h} \<union> {degree h+1..<degree u}" using deg_le by auto
    have "(\<Sum>i=0..<degree u. ?f i) = (\<Sum>i=0..degree h. ?f i) + (\<Sum>i=degree h+1 ..< degree u. ?f i)"
    unfolding set_rw by (rule sum.union_disjoint, auto)
    also have "... = (\<Sum>i=0..degree h. ?f i)" using ss0 by simp
    finally show ?thesis
      by (simp add: atLeast0AtMost atLeast0LessThan)
  qed
  also have "... = (\<Sum>i<degree u. (\<Sum>j<degree u. monom (coeff h i) 0 * monom (?B $$ (i, j)) j))"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>i<degree u. (\<Sum>j<degree u. monom (coeff h i * ?B $$ (i, j)) j))"
    by (simp add: mult_monom)
  also have "... = (\<Sum>j<degree u. (\<Sum>i<degree u. monom (coeff h i * ?B $$ (i, j)) j))"
    using sum.swap by auto
  also have "... = (\<Sum>j<degree u. monom (\<Sum>i<degree u.  (coeff h i * ?B $$ (i, j))) j)"
    by (simp add: monom_sum)
  finally have ss_rw: "(\<Sum>i<degree u. monom (coeff h i) i)
    = (\<Sum>j<degree u. monom (\<Sum>i<degree u. coeff h i * ?B $$ (i, j)) j)" .
  have coeff_eq_sum: "\<forall>i. i < degree u \<longrightarrow> coeff h i = (\<Sum>j<degree u. coeff h j * ?B $$ (j, i))"
    using poly_as_sum_eq_monoms[OF ss_rw] by fast
  have coeff_eq_sum': "\<forall>i. i < degree u \<longrightarrow> H $ i = (\<Sum>j<degree u. H $ j * ?B $$ (j, i))"
  proof (rule+)
    fix i assume i: "i < degree u"
    have "H $ i = coeff h i" by (simp add: H deg_le i vec_of_list_coeffs_replicate_nth)
    also have "... = (\<Sum>j<degree u. coeff h j * ?B $$ (j, i))" using coeff_eq_sum i by blast
    also have "... = (\<Sum>j<degree u. H $ j * ?B $$ (j, i))"
      by (rule sum.cong, auto simp add: H deg_le vec_of_list_coeffs_replicate_nth)
    finally show "H $ i = (\<Sum>j<degree u. H $ j * ?B $$ (j, i))" .
  qed
  show "(transpose_mat (?B)) *\<^sub>v H = H"
  proof (rule eq_vecI)
    fix i
    show "dim_vec (transpose_mat ?B *\<^sub>v H) = dim_vec (H)" by auto
    assume i: "i < dim_vec (H)"
    have "(transpose_mat ?B *\<^sub>v H) $ i = row (transpose_mat ?B) i \<bullet> H" using i by simp
    also have "... = (\<Sum>j = 0..<dim_vec H. ?B $$ (j, i) * H $ j)"
    proof (rule row_transpose_scalar_prod_as_sum)
      show "i < dim_col ?B" using i by simp
      show "dim_vec H = dim_row ?B" by simp
    qed
    also have "... = (\<Sum>j<degree u. H $ j * ?B $$ (j, i))" by (rule sum.cong, auto)
    also have "... = H $ i" using coeff_eq_sum'[rule_format, symmetric, of i] i by simp
    finally show "(transpose_mat ?B *\<^sub>v H) $ i = H $ i" .
  qed
 qed
qed


end


context
assumes "SORT_CONSTRAINT('a::prime_card)"
begin

lemma exists_s_factor_dvd_h_s:
fixes fi::"'a mod_ring poly"
assumes finite_P: "finite P"
      and f_desc_square_free: "f = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
      and fi_P: "fi \<in> P"
      and h: "h \<in> {v. [v^(CARD('a)) = v] (mod f)}"
      shows "\<exists>s. fi dvd (h - [:s:])"
proof -
  let ?p = "CARD('a)"
       have f_dvd_hqh: "f dvd (h^?p - h)" using h unfolding cong_def
        using mod_eq_dvd_iff_poly by blast
      also have hq_h_rw: "... = prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)"
        by (rule poly_identity_mod_p)
      finally have f_dvd_hc: "f dvd prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)" by simp
          have "fi dvd f" using f_desc_square_free fi_P
            using dvd_prod_eqI finite_P by blast
          hence "fi dvd (h^?p - h)" using dvd_trans f_dvd_hqh by auto
          also have "... = prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)" unfolding hq_h_rw by simp
          finally have fi_dvd_prod_hc: "fi dvd prod (\<lambda>c. h - [:c:]) (UNIV::'a mod_ring set)" .
          have irr_fi: "irreducible fi" using fi_P P by blast
          have fi_not_unit: "\<not> is_unit fi" using irr_fi by (simp add: irreducible\<^sub>dD(1) poly_dvd_1)
          show ?thesis using irreducible_dvd_prod[OF _ fi_dvd_prod_hc] irr_fi by auto
qed


corollary exists_unique_s_factor_dvd_h_s:
  fixes fi::"'a mod_ring poly"
  assumes finite_P: "finite P"
    and f_desc_square_free: "f = (\<Prod>a\<in>P. a)"
    and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
    and fi_P: "fi \<in> P"
    and h: "h \<in> {v. [v^(CARD('a)) = v] (mod f)}"
    shows "\<exists>!s. fi dvd (h - [:s:])"
proof -
  obtain c where fi_dvd: "fi dvd (h - [:c:])" using assms exists_s_factor_dvd_h_s by blast
  have irr_fi: "irreducible fi" using fi_P P by blast
  have fi_not_unit: "\<not> is_unit fi"
    by (simp add: irr_fi irreducible\<^sub>dD(1) poly_dvd_1)
  show ?thesis
  proof (rule ex1I[of _ c], auto simp add: fi_dvd)
    fix c2 assume fi_dvd_hc2: "fi dvd h - [:c2:]"
    have *: "fi dvd (h - [:c:]) * (h - [:c2:])" using fi_dvd by auto
    hence "fi dvd (h - [:c:]) \<or> fi dvd (h - [:c2:])"
      using irr_fi by auto
    thus "c2 = c"
      using coprime_h_c_poly coprime_not_unit_not_dvd fi_dvd fi_dvd_hc2 fi_not_unit by blast
  qed
qed


lemma exists_two_distint: "\<exists>a b::'a mod_ring. a \<noteq> b"
by (rule exI[of _ 0], rule exI[of _ 1], auto)


lemma coprime_cong_mult_factorization_poly:
  fixes f::"'b::{field} poly"
    and a b p :: "'c :: {field_gcd} poly"
  assumes finite_P: "finite P"
    and P: "P \<subseteq> {q. irreducible q}"
    and p: "\<forall>p\<in>P. [a=b] (mod p)"
    and coprime_P: "\<forall>p1 p2. p1 \<in> P \<and> p2 \<in> P \<and> p1 \<noteq> p2 \<longrightarrow> coprime p1 p2"
  shows "[a = b] (mod (\<Prod>a\<in>P. a))"
using finite_P P p coprime_P
proof (induct P)
  case empty
  thus ?case by simp
next
  case (insert p P)
  have ab_mod_pP: "[a=b] (mod (p * \<Prod>P))"
  proof (rule coprime_cong_mult_poly)
    show "[a = b] (mod p)" using insert.prems by auto
    show "[a = b] (mod \<Prod>P)" using insert.prems insert.hyps by auto
    from insert show "Rings.coprime p (\<Prod>P)"
      by (auto intro: prod_coprime_right)
  qed
  thus ?case by (simp add: insert.hyps(1) insert.hyps(2))
qed

end


context
assumes "SORT_CONSTRAINT('a::prime_card)"
begin


lemma W_eq_berlekamp_mat:
fixes u::"'a mod_ring poly"
shows "{v. [v^CARD('a) = v] (mod u) \<and> degree v < degree u}
  = {h. let H = vec_of_list ((coeffs h) @ replicate (degree u - length (coeffs h)) 0) in
    (transpose_mat (berlekamp_mat u)) *\<^sub>v H = H \<and> degree h < degree u}"
  using equation_13 by (auto simp add: Let_def)

lemma transpose_minus_1:
  assumes "dim_row Q = dim_col Q"
  shows "transpose_mat (Q - (1\<^sub>m (dim_row Q))) =  (transpose_mat Q - (1\<^sub>m (dim_row Q)))"
  using assms
  unfolding mat_eq_iff by auto

lemma system_iff:
fixes v::"'b::comm_ring_1 vec"
assumes sq_Q: "dim_row Q = dim_col Q" and v: "dim_row Q = dim_vec v"
shows "(transpose_mat Q *\<^sub>v v = v) \<longleftrightarrow> ((transpose_mat Q - 1\<^sub>m (dim_row Q)) *\<^sub>v v = 0\<^sub>v (dim_vec v))"
proof -
  have t1:"transpose_mat Q *\<^sub>v v - v = 0\<^sub>v (dim_vec v) \<Longrightarrow> (transpose_mat Q - 1\<^sub>m (dim_row Q)) *\<^sub>v v = 0\<^sub>v (dim_vec v)"
    by (subst minus_mult_distrib_mat_vec, insert sq_Q[symmetric] v, auto)
  have t2:"(transpose_mat Q - 1\<^sub>m (dim_row Q)) *\<^sub>v v = 0\<^sub>v (dim_vec v) \<Longrightarrow> transpose_mat Q *\<^sub>v v - v = 0\<^sub>v (dim_vec v)"
    by (subst (asm) minus_mult_distrib_mat_vec, insert sq_Q[symmetric] v, auto)
  have "transpose_mat Q *\<^sub>v v - v = v - v \<Longrightarrow> transpose_mat Q *\<^sub>v v = v"
  proof -
   assume a1: "transpose_mat Q *\<^sub>v v - v = v - v"
   have f2: "transpose_mat Q *\<^sub>v v \<in> carrier_vec (dim_vec v)"
     by (metis dim_mult_mat_vec index_transpose_mat(2) sq_Q v carrier_vec_dim_vec)
   then have f3: "0\<^sub>v (dim_vec v) + transpose_mat Q *\<^sub>v v = transpose_mat Q *\<^sub>v v"
     by (meson left_zero_vec)
   have f4: "0\<^sub>v (dim_vec v) = transpose_mat Q *\<^sub>v v - v"
     using a1 by auto
   have f5: "- v \<in> carrier_vec (dim_vec v)"
     by simp
   then have f6: "- v + transpose_mat Q *\<^sub>v v = v - v"
     using f2 a1 using comm_add_vec minus_add_uminus_vec by fastforce
   have "v - v = - v + v" by auto
   then have "transpose_mat Q *\<^sub>v v = transpose_mat Q *\<^sub>v v - v + v"
     using f6 f4 f3 f2 by (metis (no_types, lifting) a1 assoc_add_vec comm_add_vec f5 carrier_vec_dim_vec)
   then show ?thesis
     using a1 by auto
  qed
  hence "(transpose_mat Q *\<^sub>v v = v) = ((transpose_mat Q *\<^sub>v v) - v = v - v)" by auto
  also have "... = ((transpose_mat Q *\<^sub>v v) - v = 0\<^sub>v (dim_vec v))" by auto
  also have "... = ((transpose_mat Q - 1\<^sub>m (dim_row Q)) *\<^sub>v v = 0\<^sub>v (dim_vec v))"
    using t1 t2 by auto
  finally show ?thesis.
qed


lemma system_if_mat_kernel:
assumes sq_Q: "dim_row Q = dim_col Q" and v: "dim_row Q = dim_vec v"
shows "(transpose_mat Q *\<^sub>v v = v) \<longleftrightarrow> v \<in> mat_kernel (transpose_mat (Q - (1\<^sub>m (dim_row Q))))"
proof -
  have "(transpose_mat Q *\<^sub>v v = v) = ((transpose_mat Q - 1\<^sub>m (dim_row Q)) *\<^sub>v v = 0\<^sub>v (dim_vec v))"
    using assms system_iff by blast
  also have "... = (v \<in> mat_kernel (transpose_mat (Q - (1\<^sub>m (dim_row Q)))))"
    unfolding mat_kernel_def unfolding transpose_minus_1[OF sq_Q] unfolding v by auto
  finally show ?thesis .
qed



lemma degree_u_mod_irreducible\<^sub>d_factor_0:
fixes v and u::"'a mod_ring poly"
defines W: "W \<equiv> {v. [v ^ CARD('a) = v] (mod u)}"
assumes v: "v \<in> W"
and finite_U: "finite U" and u_U: "u = \<Prod>U" and U_irr_monic: "U \<subseteq> {q. irreducible q \<and> monic q}"
and fi_U: "fi \<in> U"
shows "degree (v mod fi) = 0"
proof -
  have deg_fi: "degree fi > 0"
    using U_irr_monic
    using fi_U irreducible\<^sub>dD[of fi] by auto
  have "fi dvd u"
    using u_U U_irr_monic finite_U dvd_prod_eqI fi_U by blast
  moreover have "u dvd (v^CARD('a) - v)"
    using v unfolding W cong_def
    by (simp add: mod_eq_dvd_iff_poly)
  ultimately have "fi dvd (v^CARD('a) - v)"
    by (rule dvd_trans)
  then have fi_dvd_prod_vc: "fi dvd prod (\<lambda>c. v - [:c:]) (UNIV::'a mod_ring set)"
    by (simp add: poly_identity_mod_p)
  have irr_fi: "irreducible fi" using fi_U U_irr_monic by blast
  have fi_not_unit: "\<not> is_unit fi"
    using irr_fi
    by (auto simp: poly_dvd_1)
  have fi_dvd_vc: "\<exists>c. fi dvd v - [:c:]"
    using irreducible_dvd_prod[OF _ fi_dvd_prod_vc] irr_fi by auto
  from this obtain a where "fi dvd v - [:a:]" by blast
  hence "v mod fi = [:a:] mod fi" using mod_eq_dvd_iff_poly by blast
  also have "... = [:a:]" by (simp add: deg_fi mod_poly_less)
  finally show ?thesis by simp
qed


(* Also polynomials over a field as a vector space in HOL-Algebra.*)

definition "poly_abelian_monoid
  = \<lparr>carrier = UNIV::'a mod_ring poly set, monoid.mult = ((*)), one = 1, zero = 0, add = (+), module.smult = smult\<rparr>"

interpretation vector_space_poly: vectorspace class_ring poly_abelian_monoid
  rewrites [simp]: "\<zero>\<^bsub>poly_abelian_monoid\<^esub> = 0"
       and [simp]: "\<one>\<^bsub>poly_abelian_monoid\<^esub> = 1"
       and [simp]: "(\<oplus>\<^bsub>poly_abelian_monoid\<^esub>) = (+)"
       and [simp]: "(\<otimes>\<^bsub>poly_abelian_monoid\<^esub>) = (*)"
       and [simp]: "carrier poly_abelian_monoid = UNIV"
       and [simp]: "(\<odot>\<^bsub>poly_abelian_monoid\<^esub>) = smult"
  apply unfold_locales
  apply (auto simp: poly_abelian_monoid_def class_field_def smult_add_left smult_add_right Units_def)
  by (metis add.commute add.right_inverse)

lemma subspace_Berlekamp:
assumes f: "degree f \<noteq> 0"
shows "subspace (class_ring :: 'a mod_ring ring) 
  {v. [v^(CARD('a)) = v] (mod f) \<and> (degree v < degree f)} poly_abelian_monoid"
proof -
  { fix v :: "'a mod_ring poly" and w :: "'a mod_ring poly"
    assume a1: "v ^ card (UNIV::'a set) mod f = v mod f"
    assume "w ^ card (UNIV::'a set) mod f = w mod f"
    then have "(v ^ card (UNIV::'a set) + w ^ card (UNIV::'a set)) mod f = (v + w) mod f"
      using a1 by (meson mod_add_cong)
    then have "(v + w) ^ card (UNIV::'a set) mod f = (v + w) mod f"
      by (simp add: add_power_poly_mod_ring)
  } note r=this
  thus ?thesis using f
   by (unfold_locales, auto simp: zero_power mod_smult_left smult_power cong_def degree_add_less)
qed


lemma berlekamp_resulting_mat_closed[simp]:
  "berlekamp_resulting_mat u \<in> carrier_mat (degree u) (degree u)"
  "dim_row (berlekamp_resulting_mat u) = degree u"
  "dim_col (berlekamp_resulting_mat u) = degree u"
proof -
  let ?A="(transpose_mat (mat (degree u) (degree u)
             (\<lambda>(i, j). if i = j then berlekamp_mat u $$ (i, j) - 1 else berlekamp_mat u $$ (i, j))))"
  let ?G="(gauss_jordan_single ?A)"
  have "?G \<in>carrier_mat (degree u) (degree u)"
    by (rule gauss_jordan_single(2)[of ?A], auto)
  thus
    "berlekamp_resulting_mat u \<in> carrier_mat (degree u) (degree u)"
    "dim_row (berlekamp_resulting_mat u) = degree u"
    "dim_col (berlekamp_resulting_mat u) = degree u"
    unfolding berlekamp_resulting_mat_def Let_def by auto
qed


(*find_base vectors returns a basis:*)
lemma berlekamp_resulting_mat_basis:
"kernel.basis (degree u) (berlekamp_resulting_mat u) (set (find_base_vectors (berlekamp_resulting_mat u)))"
proof (rule find_base_vectors(3))
  show "berlekamp_resulting_mat u \<in> carrier_mat (degree u) (degree u)" by simp
  let ?A="(transpose_mat (mat (degree u) (degree u)
          (\<lambda>(i, j). if i = j then berlekamp_mat u $$ (i, j) - 1 else berlekamp_mat u $$ (i, j))))"
  have "row_echelon_form (gauss_jordan_single ?A)"
    by (rule gauss_jordan_single(3)[of ?A], auto)
  thus "row_echelon_form (berlekamp_resulting_mat u)"
    unfolding berlekamp_resulting_mat_def Let_def by auto
qed


lemma set_berlekamp_basis_eq: "(set (berlekamp_basis u))
  = (Poly \<circ> list_of_vec)` (set (find_base_vectors (berlekamp_resulting_mat u)))"
  by (auto simp add: image_def o_def berlekamp_basis_def)


lemma berlekamp_resulting_mat_constant:
assumes deg_u: "degree u = 0"
shows "berlekamp_resulting_mat u = 1\<^sub>m 0"
  by (unfold mat_eq_iff, auto simp add: deg_u)

context
  fixes u::"'a::prime_card mod_ring poly"
begin

lemma set_berlekamp_basis_constant:
assumes deg_u: "degree u = 0"
shows "set (berlekamp_basis u) = {}"
proof -
  have one_carrier: "1\<^sub>m 0 \<in> carrier_mat 0 0" by auto
  have m: "mat_kernel (1\<^sub>m 0) = {(0\<^sub>v 0) :: 'a mod_ring vec}" unfolding mat_kernel_def by auto
  have r: "row_echelon_form (1\<^sub>m 0 :: 'a mod_ring mat)"
    unfolding row_echelon_form_def pivot_fun_def Let_def by auto
  have "set (find_base_vectors (1\<^sub>m 0)) \<subseteq> {0\<^sub>v 0 :: 'a mod_ring vec}"
    using find_base_vectors(1)[OF r one_carrier] unfolding m .
  hence "set (find_base_vectors (1\<^sub>m 0) :: 'a mod_ring vec list) = {}"
    using find_base_vectors(2)[OF r one_carrier]
    using subset_singletonD by fastforce
  thus ?thesis
    unfolding set_berlekamp_basis_eq  unfolding berlekamp_resulting_mat_constant[OF deg_u] by auto
qed

(*Maybe [simp]*)
lemma row_echelon_form_berlekamp_resulting_mat: "row_echelon_form (berlekamp_resulting_mat u)"
  by (rule gauss_jordan_single(3), auto simp add: berlekamp_resulting_mat_def Let_def)

lemma mat_kernel_berlekamp_resulting_mat_degree_0:
assumes d: "degree u = 0"
shows "mat_kernel (berlekamp_resulting_mat u) = {0\<^sub>v 0}"
  by (auto simp add: mat_kernel_def mult_mat_vec_def d)


lemma in_mat_kernel_berlekamp_resulting_mat:
assumes x: "transpose_mat (berlekamp_mat u) *\<^sub>v x = x"
and x_dim: "x \<in> carrier_vec (degree u)"
shows "x \<in> mat_kernel (berlekamp_resulting_mat u)"
proof -
 let ?QI="(mat(dim_row (berlekamp_mat u)) (dim_row (berlekamp_mat u))
         (\<lambda>(i, j). if i = j then berlekamp_mat u $$ (i, j) - 1 else berlekamp_mat u $$ (i, j)))"
  have *: "(transpose_mat (berlekamp_mat u) - 1\<^sub>m (degree u)) = transpose_mat  ?QI" by auto
  have "(transpose_mat (berlekamp_mat u) - 1\<^sub>m (dim_row (berlekamp_mat u))) *\<^sub>v x = 0\<^sub>v (dim_vec x)"
    using system_iff[of "berlekamp_mat u" x] x_dim x by auto
  hence "transpose_mat ?QI *\<^sub>v x = 0\<^sub>v (degree u)" using x_dim * by auto
  hence "berlekamp_resulting_mat u *\<^sub>v x = 0\<^sub>v (degree u)"
    unfolding berlekamp_resulting_mat_def Let_def
    using gauss_jordan_single(1)[of "transpose_mat ?QI" "degree u" "degree u" _ x] x_dim by auto
  thus ?thesis by (auto simp add: mat_kernel_def x_dim)
qed

private abbreviation "V \<equiv> kernel.VK (degree u) (berlekamp_resulting_mat u)"
private abbreviation "W \<equiv> vector_space_poly.vs 
  {v. [v^(CARD('a)) = v] (mod u) \<and> (degree v < degree u)}"

interpretation V: vectorspace class_ring V
proof -
  interpret k: kernel "(degree u)" "(degree u)" "(berlekamp_resulting_mat u)"
    by (unfold_locales; auto)
  show "vectorspace class_ring V" by intro_locales
qed

lemma linear_Poly_list_of_vec:
shows "(Poly \<circ> list_of_vec) \<in> module_hom class_ring V (vector_space_poly.vs {v. [v^(CARD('a)) = v] (mod u)})"
proof (auto simp add: LinearCombinations.module_hom_def Matrix.module_vec_def)
  fix m1 m2::" 'a mod_ring vec"
  assume m1: "m1 \<in> mat_kernel (berlekamp_resulting_mat u)"
  and m2: "m2 \<in> mat_kernel (berlekamp_resulting_mat u)"
  have m1_rw: "list_of_vec m1 = map (\<lambda>n. m1 $ n) [0..<dim_vec m1]"
    by (transfer, auto simp add: mk_vec_def)
  have m2_rw: "list_of_vec m2 = map (\<lambda>n. m2 $ n) [0..<dim_vec m2]"
    by (transfer, auto simp add: mk_vec_def)
  have "m1 \<in> carrier_vec (degree u)" by (rule mat_kernelD(1)[OF _ m1], auto)
  moreover have "m2 \<in> carrier_vec (degree u)" by (rule mat_kernelD(1)[OF _ m2], auto)
  ultimately have dim_eq: "dim_vec m1 = dim_vec m2" by auto
  show "Poly (list_of_vec (m1 + m2)) = Poly (list_of_vec m1) + Poly (list_of_vec m2)"
    unfolding poly_eq_iff m1_rw m2_rw plus_vec_def
    using dim_eq
    by (transfer', auto simp add: mk_vec_def nth_default_def)
next
  fix r m assume m: "m \<in> mat_kernel (berlekamp_resulting_mat u)"
  show "Poly (list_of_vec (r \<cdot>\<^sub>v m)) = smult r (Poly (list_of_vec m))"
    unfolding poly_eq_iff list_of_vec_rw_map[of m] smult_vec_def
    by (transfer', auto simp add: mk_vec_def nth_default_def)
next
  fix x assume x: "x \<in> mat_kernel (berlekamp_resulting_mat u)"
  show "[Poly (list_of_vec x) ^ CARD('a) = Poly (list_of_vec x)] (mod u)"
  proof (cases "degree u = 0")
    case True
    have "mat_kernel (berlekamp_resulting_mat u) = {0\<^sub>v 0}"
      by (rule mat_kernel_berlekamp_resulting_mat_degree_0[OF True])
    hence x_0: "x = 0\<^sub>v 0" using x by blast
    show ?thesis by (auto simp add: zero_power x_0 cong_def)
  next
    case False note deg_u = False
    show ?thesis
    proof -
      let ?QI="(mat (degree u) (degree u)
      (\<lambda>(i, j). if i = j then berlekamp_mat u $$ (i, j) - 1 else berlekamp_mat u $$ (i, j)))"
      let ?H="vec_of_list (coeffs (Poly (list_of_vec x)) @ replicate (degree u - length (coeffs (Poly (list_of_vec x)))) 0)"
      have x_dim: "dim_vec x = degree u" using x unfolding mat_kernel_def by auto
      hence x_carrier[simp]: "x \<in> carrier_vec (degree u)" by (metis carrier_vec_dim_vec)
      have x_kernel: "berlekamp_resulting_mat u *\<^sub>v x = 0\<^sub>v (degree u)"
        using x unfolding mat_kernel_def by auto
      have t_QI_x_0: "(transpose_mat ?QI) *\<^sub>v x = 0\<^sub>v (degree u)"
        using gauss_jordan_single(1)[of "(transpose_mat ?QI)" "degree u" "degree u" "gauss_jordan_single (transpose_mat ?QI)" x]
        using x_kernel unfolding berlekamp_resulting_mat_def Let_def by auto
      have l: "(list_of_vec x) \<noteq> []"
        by (auto simp add: list_of_vec_rw_map vec_of_dim_0[symmetric] deg_u x_dim)
      have deg_le: "degree (Poly (list_of_vec x)) < degree u"
        using degree_Poly_list_of_vec
        using x_carrier deg_u by blast
      show "[Poly (list_of_vec x) ^ CARD('a) = Poly (list_of_vec x)] (mod u)"
      proof (unfold equation_13[OF deg_le])
        have QR_rw: "?QI = berlekamp_mat u - 1\<^sub>m (dim_row (berlekamp_mat u))" by auto
        have "dim_row (berlekamp_mat u) = dim_vec ?H"
          by (auto, metis le_add_diff_inverse length_list_of_vec length_strip_while_le x_dim)
        moreover have "?H \<in> mat_kernel (transpose_mat (berlekamp_mat u - 1\<^sub>m (dim_row (berlekamp_mat u))))"
        proof -
           have Hx: "?H = x"
           proof (unfold vec_eq_iff, auto)
             let ?H'="vec_of_list (strip_while ((=) 0) (list_of_vec x)
              @ replicate (degree u - length (strip_while ((=) 0) (list_of_vec x))) 0)"
             show "length (strip_while ((=) 0) (list_of_vec x))
              + (degree u - length (strip_while ((=) 0) (list_of_vec x))) = dim_vec x"
                by (metis le_add_diff_inverse length_list_of_vec length_strip_while_le x_dim)
             fix i assume i: "i < dim_vec x"
             have "?H $ i =  coeff (Poly (list_of_vec x)) i"
             proof (rule vec_of_list_coeffs_replicate_nth[OF _ deg_le])
              show "i \<in> {..<degree u}"  using x_dim i by (auto, linarith)
             qed
             also have "... = x $ i" by (rule coeff_Poly_list_of_vec_nth'[OF i])
             finally show "?H' $ i = x $ i" by auto
           qed
           have "?H \<in> carrier_vec (degree u)" using deg_le dim_vec_of_list_h Hx by auto
           moreover have "transpose_mat (berlekamp_mat u - 1\<^sub>m (degree u)) *\<^sub>v ?H = 0\<^sub>v (degree u)"
            using t_QI_x_0 Hx QR_rw by auto
           ultimately show ?thesis
            by (auto simp add: mat_kernel_def)
        qed
        ultimately show "transpose_mat (berlekamp_mat u) *\<^sub>v ?H = ?H"
          using system_if_mat_kernel[of "berlekamp_mat u" ?H]
          by auto
        qed
     qed
   qed
qed


lemma linear_Poly_list_of_vec':
  assumes "degree u > 0"
  shows "(Poly \<circ> list_of_vec) \<in> module_hom R V W"
proof (auto simp add: LinearCombinations.module_hom_def Matrix.module_vec_def)
  fix m1 m2::" 'a mod_ring vec"
  assume m1: "m1 \<in> mat_kernel (berlekamp_resulting_mat u)"
  and m2: "m2 \<in> mat_kernel (berlekamp_resulting_mat u)"
  have m1_rw: "list_of_vec m1 = map (\<lambda>n. m1 $ n) [0..<dim_vec m1]"
    by (transfer, auto simp add: mk_vec_def)
  have m2_rw: "list_of_vec m2 = map (\<lambda>n. m2 $ n) [0..<dim_vec m2]"
    by (transfer, auto simp add: mk_vec_def)
  have "m1 \<in> carrier_vec (degree u)" by (rule mat_kernelD(1)[OF _ m1], auto)
  moreover have "m2 \<in> carrier_vec (degree u)" by (rule mat_kernelD(1)[OF _ m2], auto)
  ultimately have dim_eq: "dim_vec m1 = dim_vec m2" by auto
  show "Poly (list_of_vec (m1 + m2)) = Poly (list_of_vec m1) + Poly (list_of_vec m2)"
    unfolding poly_eq_iff m1_rw m2_rw plus_vec_def
    using dim_eq
    by (transfer', auto simp add: mk_vec_def nth_default_def)
next
  fix r m assume m: "m \<in> mat_kernel (berlekamp_resulting_mat u)"
  show "Poly (list_of_vec (r \<cdot>\<^sub>v m)) = smult r (Poly (list_of_vec m))"
    unfolding poly_eq_iff list_of_vec_rw_map[of m] smult_vec_def
    by (transfer', auto simp add: mk_vec_def nth_default_def)
next
  fix x assume x: "x \<in> mat_kernel (berlekamp_resulting_mat u)"
  show "[Poly (list_of_vec x) ^ CARD('a) = Poly (list_of_vec x)] (mod u)"
  proof (cases "degree u = 0")
    case True
    have "mat_kernel (berlekamp_resulting_mat u) = {0\<^sub>v 0}"
      by (rule mat_kernel_berlekamp_resulting_mat_degree_0[OF True])
    hence x_0: "x = 0\<^sub>v 0" using x by blast
    show ?thesis by (auto simp add: zero_power x_0 cong_def)
  next
    case False note deg_u = False
    show ?thesis
    proof -
      let ?QI="(mat (degree u) (degree u)
      (\<lambda>(i, j). if i = j then berlekamp_mat u $$ (i, j) - 1 else berlekamp_mat u $$ (i, j)))"
      let ?H="vec_of_list (coeffs (Poly (list_of_vec x)) @ replicate (degree u - length (coeffs (Poly (list_of_vec x)))) 0)"
      have x_dim: "dim_vec x = degree u" using x unfolding mat_kernel_def by auto
      hence x_carrier[simp]: "x \<in> carrier_vec (degree u)" by (metis carrier_vec_dim_vec)
      have x_kernel: "berlekamp_resulting_mat u *\<^sub>v x = 0\<^sub>v (degree u)"
        using x unfolding mat_kernel_def by auto
      have t_QI_x_0: "(transpose_mat ?QI) *\<^sub>v x = 0\<^sub>v (degree u)"
        using gauss_jordan_single(1)[of "(transpose_mat ?QI)" "degree u" "degree u" "gauss_jordan_single (transpose_mat ?QI)" x]
        using x_kernel unfolding berlekamp_resulting_mat_def Let_def by auto
      have l: "(list_of_vec x) \<noteq> []"
        by (auto simp add: list_of_vec_rw_map vec_of_dim_0[symmetric] deg_u x_dim)
      have deg_le: "degree (Poly (list_of_vec x)) < degree u"
        using degree_Poly_list_of_vec
        using x_carrier deg_u by blast
      show "[Poly (list_of_vec x) ^ CARD('a) = Poly (list_of_vec x)] (mod u)"
      proof (unfold equation_13[OF deg_le])
        have QR_rw: "?QI = berlekamp_mat u - 1\<^sub>m (dim_row (berlekamp_mat u))" by auto
        have "dim_row (berlekamp_mat u) = dim_vec ?H"
          by (auto, metis le_add_diff_inverse length_list_of_vec length_strip_while_le x_dim)
        moreover have "?H \<in> mat_kernel (transpose_mat (berlekamp_mat u - 1\<^sub>m (dim_row (berlekamp_mat u))))"
        proof -
           have Hx: "?H = x"
           proof (unfold vec_eq_iff, auto)
             let ?H'="vec_of_list (strip_while ((=) 0) (list_of_vec x)
              @ replicate (degree u - length (strip_while ((=) 0) (list_of_vec x))) 0)"
             show "length (strip_while ((=) 0) (list_of_vec x))
              + (degree u - length (strip_while ((=) 0) (list_of_vec x))) = dim_vec x"
                by (metis le_add_diff_inverse length_list_of_vec length_strip_while_le x_dim)
             fix i assume i: "i < dim_vec x"
             have "?H $ i =  coeff (Poly (list_of_vec x)) i"
             proof (rule vec_of_list_coeffs_replicate_nth[OF _ deg_le])
              show "i \<in> {..<degree u}"  using x_dim i by (auto, linarith)
             qed
             also have "... = x $ i" by (rule coeff_Poly_list_of_vec_nth'[OF i])
             finally show "?H' $ i = x $ i" by auto
           qed
           have "?H \<in> carrier_vec (degree u)" using deg_le dim_vec_of_list_h Hx by auto
           moreover have "transpose_mat (berlekamp_mat u - 1\<^sub>m (degree u)) *\<^sub>v ?H = 0\<^sub>v (degree u)"
            using t_QI_x_0 Hx QR_rw by auto
           ultimately show ?thesis
            by (auto simp add: mat_kernel_def)
        qed
        ultimately show "transpose_mat (berlekamp_mat u) *\<^sub>v ?H = ?H"
          using system_if_mat_kernel[of "berlekamp_mat u" ?H]
          by auto
        qed
     qed
   qed
next
  fix x assume x: "x \<in> mat_kernel (berlekamp_resulting_mat u)"
  show "degree (Poly (list_of_vec x)) < degree u"
    by (rule degree_Poly_list_of_vec, insert assms x, auto simp: mat_kernel_def)
qed


lemma berlekamp_basis_eq_8:
  assumes v: "v \<in> set (berlekamp_basis u)"
  shows "[v ^ CARD('a) = v] (mod u)"
proof -
  {
      fix x assume x: "x \<in> set (find_base_vectors (berlekamp_resulting_mat u))"
      have "set (find_base_vectors (berlekamp_resulting_mat u)) \<subseteq> mat_kernel (berlekamp_resulting_mat u)"
      proof (rule find_base_vectors(1))
        show "row_echelon_form (berlekamp_resulting_mat u)"
          by (rule row_echelon_form_berlekamp_resulting_mat)
        show "berlekamp_resulting_mat u \<in> carrier_mat (degree u) (degree u)" by simp
      qed
      hence "x \<in> mat_kernel (berlekamp_resulting_mat u)" using x by auto
      hence "[Poly (list_of_vec x) ^ CARD('a) = Poly (list_of_vec x)] (mod u)"
        using linear_Poly_list_of_vec
        unfolding LinearCombinations.module_hom_def Matrix.module_vec_def by auto
  }
  thus "[v ^ CARD('a) = v] (mod u)" using v unfolding set_berlekamp_basis_eq by auto
qed


lemma surj_Poly_list_of_vec:
  assumes deg_u: "degree u > 0"
  shows "(Poly \<circ> list_of_vec)` (carrier V) = carrier W"
proof (auto simp add: image_def)
  fix xa
  assume xa: "xa \<in> mat_kernel (berlekamp_resulting_mat u)"
  thus "[Poly (list_of_vec xa) ^ CARD('a) = Poly (list_of_vec xa)] (mod u)"
    using linear_Poly_list_of_vec
    unfolding LinearCombinations.module_hom_def Matrix.module_vec_def by auto
  show "degree (Poly (list_of_vec xa)) < degree u"
  proof (rule degree_Poly_list_of_vec[OF _ deg_u])
    show "xa \<in> carrier_vec (degree u)" using xa unfolding mat_kernel_def by simp
  qed
next
  fix x assume x: "[x ^ CARD('a) = x] (mod u)"
  and deg_x: "degree x < degree u"
  show "\<exists>xa \<in> mat_kernel (berlekamp_resulting_mat u). x = Poly (list_of_vec xa)"
  proof (rule bexI[of _ "vec_of_list (coeffs x @ replicate (degree u - length (coeffs x)) 0)"])
    let ?X = "vec_of_list (coeffs x @ replicate (degree u - length (coeffs x)) 0)"
    show "x = Poly (list_of_vec (vec_of_list (coeffs x @ replicate (degree u - length (coeffs x)) 0)))"
      by auto
    have X: "?X \<in> carrier_vec (degree u)" unfolding carrier_vec_def
      by (auto, metis Suc_leI coeffs_0_eq_Nil deg_x degree_0 le_add_diff_inverse
        length_coeffs_degree linordered_semidom_class.add_diff_inverse list.size(3) order.asym)
    have t: "transpose_mat (berlekamp_mat u) *\<^sub>v ?X = ?X"
      using equation_13[OF deg_x] x by auto
    show "vec_of_list (coeffs x @ replicate (degree u - length (coeffs x)) 0)
      \<in> mat_kernel (berlekamp_resulting_mat u)" by (rule in_mat_kernel_berlekamp_resulting_mat[OF t X])
  qed
qed


lemma card_set_berlekamp_basis: "card (set (berlekamp_basis u)) = length (berlekamp_basis u)"
proof -
  have b: "berlekamp_resulting_mat u \<in> carrier_mat (degree u) (degree u)" by auto
  have "(set (berlekamp_basis u)) = (Poly \<circ> list_of_vec) ` set (find_base_vectors (berlekamp_resulting_mat u))"
    unfolding set_berlekamp_basis_eq ..
  also have " card ... = card (set (find_base_vectors (berlekamp_resulting_mat u)))"
  proof (rule card_image, rule subset_inj_on[OF inj_Poly_list_of_vec])
    show "set (find_base_vectors (berlekamp_resulting_mat u)) \<subseteq> carrier_vec (degree u)"
    using find_base_vectors(1)[OF row_echelon_form_berlekamp_resulting_mat b]
    unfolding carrier_vec_def mat_kernel_def
    by auto
  qed
  also have "... =  length (find_base_vectors (berlekamp_resulting_mat u))"
    by (rule length_find_base_vectors[symmetric, OF row_echelon_form_berlekamp_resulting_mat b])
  finally show ?thesis unfolding berlekamp_basis_def by auto
qed

context
  assumes deg_u0[simp]: "degree u > 0"
begin

interpretation Berlekamp_subspace: vectorspace class_ring W
  by (rule vector_space_poly.subspace_is_vs[OF subspace_Berlekamp], simp)

lemma linear_map_Poly_list_of_vec': "linear_map class_ring V W (Poly \<circ> list_of_vec)"
proof (auto simp add: linear_map_def)
  show "vectorspace class_ring V" by intro_locales
  show "vectorspace class_ring W" by (rule Berlekamp_subspace.vectorspace_axioms)
  show "mod_hom class_ring V W (Poly \<circ> list_of_vec)"
  proof (rule mod_hom.intro, unfold mod_hom_axioms_def)
    show "module class_ring V" by intro_locales
    show "module class_ring W" using Berlekamp_subspace.vectorspace_axioms by intro_locales
    show "Poly \<circ> list_of_vec \<in> module_hom class_ring V W"
      by (rule linear_Poly_list_of_vec'[OF deg_u0])
  qed
qed

lemma berlekamp_basis_basis:
  "Berlekamp_subspace.basis (set (berlekamp_basis u))"
proof (unfold set_berlekamp_basis_eq, rule linear_map.linear_inj_image_is_basis)
  show "linear_map class_ring V W (Poly \<circ> list_of_vec)"
    by (rule linear_map_Poly_list_of_vec')
  show "inj_on (Poly \<circ> list_of_vec) (carrier V)"
  proof (rule subset_inj_on[OF inj_Poly_list_of_vec])
    show "carrier V \<subseteq> carrier_vec (degree u)"
      by (auto simp add: mat_kernel_def)
  qed
  show "(Poly \<circ> list_of_vec) ` carrier V = carrier W"
    using surj_Poly_list_of_vec[OF deg_u0] by auto
  show b: "V.basis (set (find_base_vectors (berlekamp_resulting_mat u)))"
    by (rule berlekamp_resulting_mat_basis)
  show "V.fin_dim"
  proof -
    have "finite (set (find_base_vectors (berlekamp_resulting_mat u)))" by auto
    moreover have "set (find_base_vectors (berlekamp_resulting_mat u)) \<subseteq> carrier V"
    and "V.gen_set (set (find_base_vectors (berlekamp_resulting_mat u)))"
      using b unfolding V.basis_def by auto
    ultimately show ?thesis unfolding V.fin_dim_def by auto
  qed
qed


lemma finsum_sum:
fixes f::"'a mod_ring poly"
assumes f: "finite B"
and a_Pi: "a \<in> B \<rightarrow> carrier R"
and V: "B \<subseteq> carrier W"
shows "(\<Oplus>\<^bsub>W\<^esub>v\<in>B. a v \<odot>\<^bsub>W\<^esub> v) = sum (\<lambda>v. smult (a v) v) B"
using f a_Pi V
proof (induct B)
  case empty
  thus ?case unfolding Berlekamp_subspace.module.M.finsum_empty by auto
  next
  case (insert x V)
  have hyp: "(\<Oplus>\<^bsub>W\<^esub>v \<in> V. a v \<odot>\<^bsub>W\<^esub> v) = sum (\<lambda>v. smult (a v) v) V"
  proof (rule insert.hyps)
    show "a \<in> V \<rightarrow> carrier R"
      using insert.prems unfolding class_field_def  by auto
     show "V \<subseteq> carrier W" using insert.prems by simp
  qed
  have "(\<Oplus>\<^bsub>W\<^esub>v\<in>insert x V. a v \<odot>\<^bsub>W\<^esub> v) =  (a x \<odot>\<^bsub>W\<^esub> x) \<oplus>\<^bsub>W\<^esub> (\<Oplus>\<^bsub>W\<^esub>v \<in> V. a v \<odot>\<^bsub>W\<^esub> v)"
  proof (rule abelian_monoid.finsum_insert)
    show "abelian_monoid W" by (unfold_locales)
    show "finite V" by fact
    show "x \<notin> V" by fact
    show "(\<lambda>v. a v \<odot>\<^bsub>W\<^esub> v) \<in> V \<rightarrow> carrier W"
      proof (unfold Pi_def, rule, rule allI, rule impI)
        fix v assume v: "v\<in>V"
        show "a v \<odot>\<^bsub>W\<^esub> v \<in> carrier W"
        proof (rule Berlekamp_subspace.smult_closed)
          show "a v \<in> carrier class_ring" using insert.prems v unfolding Pi_def
            by (simp add: class_field_def)
          show "v \<in> carrier W" using v insert.prems by auto
        qed
      qed
    show "a x \<odot>\<^bsub>W\<^esub> x \<in> carrier W"
    proof (rule Berlekamp_subspace.smult_closed)
      show "a x \<in> carrier class_ring" using insert.prems unfolding Pi_def
        by (simp add: class_field_def)
      show "x \<in> carrier W" using insert.prems by auto
    qed
  qed
  also have "... = (a x \<odot>\<^bsub>W\<^esub> x) + (\<Oplus>\<^bsub>W\<^esub>v \<in> V. a v \<odot>\<^bsub>W\<^esub> v)" by auto
  also have "... = (a x \<odot>\<^bsub>W\<^esub> x) + sum (\<lambda>v. smult (a v) v) V" unfolding hyp by simp
  also have "... = (smult (a x) x) + sum (\<lambda>v. smult (a v) v) V" by simp
  also have "... = sum (\<lambda>v. smult (a v) v) (insert x V)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case .
qed


lemma exists_vector_in_Berlekamp_subspace_dvd:
fixes p_i::"'a mod_ring poly"
assumes finite_P: "finite P"
      and f_desc_square_free: "u = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
      and pi: "p_i \<in> P" and pj: "p_j \<in> P" and pi_pj: "p_i \<noteq> p_j"
      and monic_f: "monic u" and sf_f: "square_free u"
      and not_irr_w: "\<not> irreducible w"
      and w_dvd_f: "w dvd u" and monic_w: "monic w"
      and pi_dvd_w: "p_i dvd w" and pj_dvd_w: "p_j dvd w"
shows "\<exists>v. v \<in> {h. [h^(CARD('a)) = h] (mod u) \<and> degree h < degree u}
  \<and> v mod p_i \<noteq> v mod p_j
  \<and> degree (v mod p_i) = 0
  \<and> degree (v mod p_j) = 0
\<comment> \<open>This implies that the algorithm decreases the degree of the reducible polynomials in each step:\<close>
  \<and> (\<exists>s. gcd w (v - [:s:]) \<noteq> w \<and> gcd w (v - [:s:]) \<noteq> 1)"
proof -
  have f_not_0: "u \<noteq> 0" using monic_f by auto
  have irr_pi: "irreducible p_i" using pi P by auto
  have irr_pj: "irreducible p_j" using pj P by auto
  obtain m and n::nat where P_m: "P = m ` {i. i < n}" and inj_on_m: "inj_on m {i. i < n}"
    using finite_imp_nat_seg_image_inj_on[OF finite_P] by blast
  hence "n = card P" by (simp add: card_image)
  have degree_prod: "degree (prod m {i. i < n}) = degree u"
    by (metis P_m f_desc_square_free inj_on_m prod.reindex_cong)
  have not_zero: "\<forall>i\<in>{i. i < n}. m i \<noteq> 0"
    using P_m f_desc_square_free f_not_0 by auto
  obtain i where mi: "m i = p_i" and i: "i < n" using P_m pi by blast
  obtain j where mj: "m j = p_j" and j: "j < n" using P_m pj by blast
  have ij: "i \<noteq> j"  using  mi mj pi_pj by auto
  obtain s_i and s_j::"'a mod_ring" where si_sj: "s_i \<noteq> s_j" using exists_two_distint by blast
  let ?u="\<lambda>x. if x = i then [:s_i:] else if x = j then [:s_j:] else [:0:]"
  have degree_si: "degree [:s_i:] = 0" by auto
  have degree_sj: "degree [:s_j:] = 0" by auto
  have "\<exists>!v. degree v < (\<Sum>i\<in>{i. i < n}. degree (m i)) \<and> (\<forall>a\<in>{i. i < n}. [v = ?u a] (mod m a))"
  proof (rule chinese_remainder_unique_poly)
    show "\<forall>a\<in>{i. i < n}. \<forall>b\<in>{i. i < n}. a \<noteq> b \<longrightarrow> Rings.coprime (m a) (m b)"
    proof (rule+)
      fix a b assume "a \<in> {i. i < n}" and "b \<in> {i. i < n}" and "a \<noteq> b"
      thus "Rings.coprime (m a) (m b)"
        using coprime_polynomial_factorization[OF P finite_P, simplified] P_m
        by (metis image_eqI inj_onD inj_on_m)
    qed
    show "\<forall>i\<in>{i. i < n}. m i \<noteq> 0" by (rule not_zero)
    show "0 < degree (prod m {i. i < n})" unfolding degree_prod using deg_u0 by blast
  qed
  from this obtain v where v: "\<forall>a\<in>{i. i < n}. [v = ?u a] (mod m a)"
  and degree_v: "degree v < (\<Sum>i\<in>{i. i < n}. degree (m i))" by blast
  show ?thesis
  proof (rule exI[of _ v], auto)
    show vp_v_mod: "[v ^ CARD('a) = v] (mod u)"
    proof (unfold f_desc_square_free, rule coprime_cong_mult_factorization_poly[OF finite_P])
      show "P \<subseteq> {q. irreducible q}" using P by blast
      show "\<forall>p\<in>P. [v ^ CARD('a) = v] (mod p)"
      proof (rule ballI)
        fix p assume p: "p \<in> P"
        hence irr_p: "irreducible\<^sub>d p" using P by auto
        obtain k where mk: "m k = p" and k: "k < n" using P_m p by blast
        have "[v = ?u k] (mod p)" using v mk k by auto
        moreover have "?u k mod p = ?u k"
          apply (rule mod_poly_less) using irreducible\<^sub>dD(1)[OF irr_p] by auto
        ultimately obtain s where v_mod_p: "v mod p = [:s:]" unfolding cong_def by force
        hence deg_v_p: "degree (v mod p) = 0" by auto
        have "v mod p = [:s:]" by (rule v_mod_p)
        also have "... = [:s:]^CARD('a)" unfolding poly_const_pow by auto
        also have "... = (v mod p) ^ CARD('a)" using v_mod_p by auto
        also have "... = (v mod p) ^ CARD('a) mod p" using calculation by auto
        also have "... = v^CARD('a) mod p" using power_mod by blast
        finally show "[v ^ CARD('a) = v] (mod p)" unfolding cong_def ..
      qed
      show "\<forall>p1 p2. p1 \<in> P \<and> p2 \<in> P \<and> p1 \<noteq> p2 \<longrightarrow> coprime p1 p2"
        using P coprime_polynomial_factorization finite_P by auto
    qed
    have "[v = ?u i] (mod m i)" using v i by auto
    hence v_pi_si_mod: "v mod p_i = [:s_i:] mod p_i" unfolding cong_def mi by auto
    also have "... = [:s_i:]" apply (rule mod_poly_less) using irr_pi by auto
    finally have v_pi_si: "v mod p_i = [:s_i:]" .

    have "[v = ?u j] (mod m j)" using v j by auto
    hence v_pj_sj_mod: "v mod p_j = [:s_j:] mod p_j" unfolding cong_def mj using ij by auto
    also have "... = [:s_j:]" apply (rule mod_poly_less) using irr_pj by auto
    finally have v_pj_sj: "v mod p_j = [:s_j:]" .
    show "v mod p_i = v mod p_j \<Longrightarrow> False" using si_sj v_pi_si v_pj_sj by auto
    show "degree (v mod p_i) = 0" unfolding v_pi_si by simp
    show "degree (v mod p_j) = 0" unfolding v_pj_sj by simp
    show "\<exists>s. gcd w (v - [:s:]) \<noteq> w \<and> gcd w (v - [:s:]) \<noteq> 1"
    proof (rule exI[of _ s_i], rule conjI)
      have pi_dvd_v_si: "p_i dvd v - [:s_i:]" using v_pi_si_mod mod_eq_dvd_iff_poly by blast
      have pj_dvd_v_sj: "p_j dvd v - [:s_j:]" using v_pj_sj_mod mod_eq_dvd_iff_poly by blast
      have w_eq: "w = prod (\<lambda>c. gcd w (v - [:c:])) (UNIV::'a mod_ring set)"
      proof (rule Berlekamp_gcd_step)
        show "[v ^ CARD('a) = v] (mod w)" using vp_v_mod cong_dvd_modulus_poly w_dvd_f by blast
        show "square_free w" by (rule square_free_factor[OF w_dvd_f sf_f])
        show "monic w" by (rule monic_w)
      qed
      show "gcd w (v - [:s_i:]) \<noteq> w"
      proof (rule ccontr, simp)
        assume gcd_w: "gcd w (v - [:s_i:]) = w"
        show False apply (rule \<open>v mod p_i = v mod p_j \<Longrightarrow> False\<close>)
        by (metis irreducibleE \<open>degree (v mod p_i) = 0\<close> gcd_greatest_iff gcd_w irr_pj is_unit_field_poly mod_eq_dvd_iff_poly mod_poly_less neq0_conv pj_dvd_w v_pi_si)
      qed
      show "gcd w (v - [:s_i:]) \<noteq> 1"
        by (metis irreducibleE gcd_greatest_iff irr_pi pi_dvd_v_si pi_dvd_w)
    qed
    show "degree v < degree u"
    proof -
      have "(\<Sum>i | i < n. degree (m i)) = degree (prod m {i. i < n})"
        by (rule degree_prod_eq_sum_degree[symmetric, OF not_zero])
      thus ?thesis using degree_v unfolding degree_prod by auto
    qed
  qed
qed



lemma exists_vector_in_Berlekamp_basis_dvd_aux:
assumes basis_V: "Berlekamp_subspace.basis B"
  and finite_V: "finite B" (*This should be removed, since the Berlekamp subspace is a finite set*)
assumes finite_P: "finite P"
      and f_desc_square_free: "u = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
      and pi: "p_i \<in> P" and pj: "p_j \<in> P" and pi_pj: "p_i \<noteq> p_j"
      and monic_f: "monic u" and sf_f: "square_free u"
      and not_irr_w: "\<not> irreducible w"
      and w_dvd_f: "w dvd u" and monic_w: "monic w"
      and pi_dvd_w: "p_i dvd w" and pj_dvd_w: "p_j dvd w"
    shows "\<exists>v \<in> B. v mod p_i \<noteq> v mod p_j"
proof (rule ccontr, auto)
  have V_in_carrier: "B \<subseteq> carrier W"
    using basis_V unfolding Berlekamp_subspace.basis_def by auto
  assume all_eq: "\<forall>v\<in>B. v mod p_i = v mod p_j"
  obtain x where x: "x \<in> {h. [h ^ CARD('a) = h] (mod u) \<and> degree h < degree u}"
      and x_pi_pj: "x mod p_i \<noteq> x mod p_j" and "degree (x mod p_i) = 0" and "degree (x mod p_j) = 0"
      "(\<exists>s. gcd w (x - [:s:]) \<noteq> w \<and> gcd w (x - [:s:]) \<noteq> 1)"
      using exists_vector_in_Berlekamp_subspace_dvd[OF _ _ _ pi pj _ _ _ _ w_dvd_f monic_w pi_dvd_w]
      assms by meson
  have x_in: "x \<in> carrier W" using x by auto
  hence "(\<exists>!a. a \<in> B \<rightarrow>\<^sub>E carrier class_ring \<and> Berlekamp_subspace.lincomb a B = x)"
    using Berlekamp_subspace.basis_criterion[OF finite_V V_in_carrier] using basis_V
    by (simp add: class_field_def)
  from this obtain a where a_Pi: "a \<in> B \<rightarrow>\<^sub>E carrier class_ring"
    and lincomb_x: "Berlekamp_subspace.lincomb a B = x"
    by blast
  have fs_ss: "(\<Oplus>\<^bsub>W\<^esub>v\<in>B. a v \<odot>\<^bsub>W\<^esub> v) = sum (\<lambda>v. smult (a v) v) B"
  proof (rule finsum_sum)
    show "finite B" by fact
    show "a \<in> B \<rightarrow> carrier class_ring" using a_Pi by auto
    show "B \<subseteq> carrier W" by (rule V_in_carrier)
  qed
  have "x mod p_i = Berlekamp_subspace.lincomb a B mod p_i" using lincomb_x by simp
  also have " ... = (\<Oplus>\<^bsub>W\<^esub>v\<in>B. a v \<odot>\<^bsub>W\<^esub> v) mod p_i" unfolding Berlekamp_subspace.lincomb_def ..
  also have "... = (sum (\<lambda>v. smult (a v) v) B) mod p_i" unfolding fs_ss ..
  also have "... = sum (\<lambda>v. smult (a v) v mod p_i) B" using finite_V poly_mod_sum by blast
  also have "... = sum (\<lambda>v. smult (a v) (v mod p_i)) B" by (meson mod_smult_left)
  also have "... = sum (\<lambda>v. smult (a v) (v mod p_j)) B" using all_eq by auto
  also have "... = sum (\<lambda>v. smult (a v) v mod p_j) B" by (metis mod_smult_left)
  also have "... = (sum (\<lambda>v. smult (a v) v) B) mod p_j"
  by (metis (mono_tags, lifting) finite_V poly_mod_sum sum.cong)
  also have "... = (\<Oplus>\<^bsub>W\<^esub>v\<in>B. a v \<odot>\<^bsub>W\<^esub> v) mod p_j" unfolding fs_ss ..
  also have "... = Berlekamp_subspace.lincomb a B mod p_j"
    unfolding Berlekamp_subspace.lincomb_def ..
  also have "... = x mod p_j" using lincomb_x by simp
  finally have "x mod p_i = x mod p_j" .
  thus False using x_pi_pj by contradiction
qed


lemma exists_vector_in_Berlekamp_basis_dvd:
assumes basis_V: "Berlekamp_subspace.basis B"
and finite_V: "finite B" (*This should be removed, since the Berlekamp subspace is a finite set*)
assumes finite_P: "finite P"
      and f_desc_square_free: "u = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
      and pi: "p_i \<in> P" and pj: "p_j \<in> P" and pi_pj: "p_i \<noteq> p_j"
      and monic_f: "monic u" and sf_f: "square_free u"
      and not_irr_w: "\<not> irreducible w"
      and w_dvd_f: "w dvd u" and monic_w: "monic w"
      and pi_dvd_w: "p_i dvd w" and pj_dvd_w: "p_j dvd w"
shows "\<exists>v \<in> B. v mod p_i \<noteq> v mod p_j
  \<and> degree (v mod p_i) = 0
  \<and> degree (v mod p_j) = 0
\<comment> \<open>This implies that the algorithm decreases the degree of the reducible polynomials in each step:\<close>
  \<and> (\<exists>s. gcd w (v - [:s:]) \<noteq> w \<and> \<not> coprime w (v - [:s:]))"
proof -
  have f_not_0: "u \<noteq> 0" using monic_f by auto
  have irr_pi: "irreducible p_i" using pi P by fast
  have irr_pj: "irreducible p_j" using pj P by fast
  obtain v where vV: "v \<in> B" and v_pi_pj: "v mod p_i \<noteq> v mod p_j"
    using assms exists_vector_in_Berlekamp_basis_dvd_aux by blast
  have v: "v \<in> {v. [v ^ CARD('a) = v] (mod u)}"
    using basis_V vV unfolding Berlekamp_subspace.basis_def by auto
  have deg_v_pi: "degree (v mod p_i) = 0"
    by (rule degree_u_mod_irreducible\<^sub>d_factor_0[OF v finite_P f_desc_square_free P pi])
  from this obtain s_i where v_pi_si: "v mod p_i = [:s_i:]" using degree_eq_zeroE by blast
  have deg_v_pj: "degree (v mod p_j) = 0"
    by (rule degree_u_mod_irreducible\<^sub>d_factor_0[OF v finite_P f_desc_square_free P pj])
  from this obtain s_j where v_pj_sj: "v mod p_j = [:s_j:]" using degree_eq_zeroE by blast
  have si_sj: "s_i \<noteq> s_j" using v_pi_si v_pj_sj v_pi_pj by auto
  have "(\<exists>s. gcd w (v - [:s:]) \<noteq> w \<and> \<not> Rings.coprime w (v - [:s:]))"
  proof (rule exI[of _ s_i], rule conjI)
    have pi_dvd_v_si: "p_i dvd v - [:s_i:]" by (metis mod_eq_dvd_iff_poly mod_mod_trivial v_pi_si)
    have pj_dvd_v_sj: "p_j dvd v - [:s_j:]" by (metis mod_eq_dvd_iff_poly mod_mod_trivial v_pj_sj)
    have w_eq: "w = prod (\<lambda>c. gcd w (v - [:c:])) (UNIV::'a mod_ring set)"
    proof (rule Berlekamp_gcd_step)
      show "[v ^ CARD('a) = v] (mod w)" using v cong_dvd_modulus_poly w_dvd_f by blast
      show "square_free w" by (rule square_free_factor[OF w_dvd_f sf_f])
      show "monic w" by (rule monic_w)
    qed
    show "gcd w (v - [:s_i:]) \<noteq> w"
      by (metis irreducibleE deg_v_pi gcd_greatest_iff irr_pj is_unit_field_poly mod_eq_dvd_iff_poly mod_poly_less neq0_conv pj_dvd_w v_pi_pj v_pi_si)
    show "\<not> Rings.coprime w (v - [:s_i:])"
      using irr_pi pi_dvd_v_si pi_dvd_w 
      by (simp add: irreducible\<^sub>dD(1) not_coprimeI)
  qed
  thus ?thesis using v_pi_pj vV deg_v_pi deg_v_pj by auto
qed

lemma exists_bijective_linear_map_W_vec:
  assumes finite_P: "finite P"
      and u_desc_square_free: "u = (\<Prod>a\<in>P. a)"
      and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
  shows "\<exists>f. linear_map class_ring W (module_vec TYPE('a mod_ring) (card P)) f
  \<and> bij_betw f (carrier W) (carrier_vec (card P)::'a mod_ring vec set)"
proof -
  let ?B="carrier_vec (card P)::'a mod_ring vec set"
  have u_not_0: "u \<noteq> 0" using deg_u0 degree_0 by force
  obtain m and n::nat where P_m: "P = m ` {i. i < n}" and inj_on_m: "inj_on m {i. i < n}"
    using finite_imp_nat_seg_image_inj_on[OF finite_P] by blast
  hence n: "n = card P" by (simp add: card_image)
  have degree_prod: "degree (prod m {i. i < n}) = degree u"
    by (metis P_m u_desc_square_free inj_on_m prod.reindex_cong)
  have not_zero: "\<forall>i\<in>{i. i < n}. m i \<noteq> 0"
    using P_m u_desc_square_free u_not_0 by auto
  have deg_sum_eq: "(\<Sum>i\<in>{i. i < n}. degree (m i)) = degree u"
    by (metis degree_prod degree_prod_eq_sum_degree not_zero)
  have coprime_mi_mj:"\<forall>i\<in>{i. i < n}. \<forall>j\<in>{i. i < n}. i \<noteq> j \<longrightarrow> coprime (m i) (m j)"
  proof (rule+)
    fix i j assume i: "i \<in> {i. i < n}"
    and j: "j \<in> {i. i < n}" and ij: "i \<noteq> j"
    show "coprime (m i) (m j)"
    proof (rule coprime_polynomial_factorization[OF P finite_P])
      show "m i \<in> P" using i P_m by auto
      show "m j \<in> P" using j P_m by auto
      show "m i \<noteq> m j" using inj_on_m i ij j unfolding inj_on_def by blast
    qed
  qed
  let ?f = "\<lambda>v. vec n (\<lambda>i. coeff (v mod (m i)) 0)"
  interpret vec_VS: vectorspace class_ring "(module_vec TYPE('a mod_ring) n)"
    by (rule VS_Connect.vec_vs)
  interpret linear_map class_ring W "(module_vec TYPE('a mod_ring) n)" ?f
    by (intro_locales, unfold mod_hom_axioms_def LinearCombinations.module_hom_def,
        auto simp add: vec_eq_iff module_vec_def mod_smult_left poly_mod_add_left)
  have "linear_map class_ring W (module_vec TYPE('a mod_ring) n) ?f"
    by (intro_locales)
  moreover have inj_f: "inj_on ?f (carrier W)"
  proof (rule Ke0_imp_inj, auto simp add: mod_hom.ker_def)
     show "[0 ^ CARD('a) = 0] (mod u)" by (simp add: cong_def zero_power)
     show "vec n (\<lambda>i. 0) = \<zero>\<^bsub>module_vec TYPE('a mod_ring) n\<^esub>" by (auto simp add: module_vec_def)
     fix x assume x: "[x ^ CARD('a) = x] (mod u)" and deg_x: "degree x < degree u"
     and v: "vec n (\<lambda>i. coeff (x mod m i) 0) = \<zero>\<^bsub>module_vec TYPE('a mod_ring) n\<^esub>"
     have cong_0: "\<forall>i\<in>{i. i < n}. [x = (\<lambda>i. 0) i] (mod m i)"
     proof (rule, unfold cong_def)
       fix i assume i: "i \<in> {i. i < n}"
       have deg_x_mod_mi: "degree (x mod m i) = 0"
       proof (rule degree_u_mod_irreducible\<^sub>d_factor_0[OF _ finite_P u_desc_square_free P])
          show "x \<in> {v. [v ^ CARD('a) = v] (mod u)}" using x by auto
          show "m i \<in> P" using P_m i by auto
       qed
       thus "x mod m i = 0 mod m i"
        using v
        unfolding module_vec_def
        by (auto, metis i leading_coeff_neq_0 mem_Collect_eq index_vec index_zero_vec(1))
     qed
     moreover have deg_x2: "degree x < (\<Sum>i\<in>{i. i < n}. degree (m i))"
      using deg_sum_eq deg_x by simp
     moreover have "\<forall>i\<in>{i. i < n}. [0 = (\<lambda>i. 0) i] (mod m i)"
      by (auto simp add: cong_def)
     moreover have "degree 0 < (\<Sum>i\<in>{i. i < n}. degree (m i))"
      using degree_prod deg_sum_eq deg_u0 by force
     moreover have "\<exists>!x. degree x < (\<Sum>i\<in>{i. i < n}. degree (m i))
        \<and> (\<forall>i\<in>{i. i < n}. [x = (\<lambda>i. 0) i] (mod m i))"
     proof (rule chinese_remainder_unique_poly[OF not_zero])
      show "0 < degree (prod m {i. i < n})"
        using deg_u0 degree_prod by linarith
     qed (insert coprime_mi_mj, auto)
     ultimately show "x = 0" by blast
  qed
  moreover have "?f ` (carrier W) = ?B"
  proof (auto simp add: image_def)
    fix xa
    show "n = card P" by (auto simp add: n)
    next
    fix x::"'a mod_ring vec" assume x: "x \<in> carrier_vec (card P)"
    have " \<exists>!v. degree v < (\<Sum>i\<in>{i. i < n}. degree (m i)) \<and> (\<forall>i\<in>{i. i < n}. [v = (\<lambda>i. [:x $ i:]) i] (mod m i))"
    proof (rule chinese_remainder_unique_poly[OF not_zero])
      show "0 < degree (prod m {i. i < n})"
        using deg_u0 degree_prod by linarith
    qed (insert coprime_mi_mj, auto)
    from this obtain v where deg_v: "degree v < (\<Sum>i\<in>{i. i < n}. degree (m i))"
      and v_x_cong: "(\<forall>i \<in> {i. i < n}. [v = (\<lambda>i. [:x $ i:]) i] (mod m i))" by auto
    show "\<exists>xa. [xa ^ CARD('a) = xa] (mod u) \<and> degree xa < degree u
      \<and> x = vec n (\<lambda>i. coeff (xa mod m i) 0)"
    proof (rule exI[of _ v], auto)
      show v: "[v ^ CARD('a) = v] (mod u)"
      proof (unfold u_desc_square_free, rule coprime_cong_mult_factorization_poly[OF finite_P], auto)
        fix y assume y: "y \<in> P" thus "irreducible y" using P by blast
        obtain i where i: "i \<in> {i. i < n}" and mi: "y = m i" using P_m y by blast
        have "irreducible (m i)" using i P_m P by auto
        moreover have "[v = [:x $ i:]] (mod m i)" using v_x_cong i by auto
        ultimately have v_mi_eq_xi: "v mod m i = [:x $ i:]"
          by (auto simp: cong_def intro!: mod_poly_less)
        have xi_pow_xi: "[:x $ i:]^CARD('a) = [:x $ i:]" by (simp add: poly_const_pow)
        hence "(v mod m i)^CARD('a) = v mod m i" using v_mi_eq_xi by auto
        hence "(v mod m i)^CARD('a) = (v^CARD('a) mod m i)"
          by (metis mod_mod_trivial power_mod)
        thus "[v ^ CARD('a) = v] (mod y)" unfolding mi cong_def v_mi_eq_xi xi_pow_xi by simp
      next
        fix p1 p2 assume "p1 \<in> P" and "p2 \<in> P" and "p1 \<noteq> p2"
        then show "Rings.coprime p1 p2"
          using coprime_polynomial_factorization[OF P finite_P] by auto
      qed
      show "degree v < degree u" using deg_v deg_sum_eq degree_prod by presburger
      show "x = vec n (\<lambda>i. coeff (v mod m i) 0)"
      proof (unfold vec_eq_iff, rule conjI)
         show "dim_vec x = dim_vec (vec n (\<lambda>i. coeff (v mod m i) 0))" using x n by simp
         show "\<forall>i<dim_vec (vec n (\<lambda>i. coeff (v mod m i) 0)). x $ i = vec n (\<lambda>i. coeff (v mod m i) 0) $ i"
         proof (auto)
           fix i assume i: "i < n"
           have deg_mi: "irreducible (m i)" using i P_m P by auto
           have deg_v_mi: "degree (v mod m i) = 0"
           proof (rule degree_u_mod_irreducible\<^sub>d_factor_0[OF _ finite_P u_desc_square_free P])
              show "v \<in> {v. [v ^ CARD('a) = v] (mod u)}" using v by fast
              show "m i \<in> P" using P_m i by auto
           qed
           have "v mod m i = [:x $ i:] mod m i" using v_x_cong i unfolding cong_def by auto
           also have "... = [:x $ i:]" using deg_mi by (auto intro!: mod_poly_less)
           finally show "x $ i = coeff (v mod m i) 0" by simp
         qed
      qed
    qed
  qed
  ultimately show ?thesis unfolding bij_betw_def n by auto
qed

lemma fin_dim_kernel_berlekamp: "V.fin_dim"
proof -
  have "finite (set (find_base_vectors (berlekamp_resulting_mat u)))" by auto
  moreover have "set (find_base_vectors (berlekamp_resulting_mat u)) \<subseteq> carrier V"
  and "V.gen_set (set (find_base_vectors (berlekamp_resulting_mat u)))"
    using berlekamp_resulting_mat_basis[of u] unfolding V.basis_def by auto
  ultimately show ?thesis unfolding V.fin_dim_def by auto
qed

lemma Berlekamp_subspace_fin_dim: "Berlekamp_subspace.fin_dim"
proof (rule linear_map.surj_fin_dim[OF linear_map_Poly_list_of_vec'])
  show "(Poly \<circ> list_of_vec) ` carrier V = carrier W"
    using surj_Poly_list_of_vec[OF deg_u0] by auto
  show "V.fin_dim" by (rule fin_dim_kernel_berlekamp)
qed

context
  fixes P
  assumes finite_P: "finite P"
  and u_desc_square_free: "u = (\<Prod>a\<in>P. a)"
  and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
begin

interpretation RV: vec_space "TYPE('a mod_ring)" "card P" .

lemma Berlekamp_subspace_eq_dim_vec: "Berlekamp_subspace.dim = RV.dim"
proof -
  obtain f where lm_f: "linear_map class_ring W (module_vec TYPE('a mod_ring) (card P)) f"
  and bij_f: "bij_betw f (carrier W) (carrier_vec (card P)::'a mod_ring vec set)"
    using exists_bijective_linear_map_W_vec[OF finite_P u_desc_square_free P] by blast
  show ?thesis
  proof (rule linear_map.dim_eq[OF lm_f Berlekamp_subspace_fin_dim])
    show "inj_on f (carrier W)" by (rule bij_betw_imp_inj_on[OF bij_f])
    show " f ` carrier W = carrier RV.V" using bij_f unfolding bij_betw_def by auto
  qed
qed


lemma Berlekamp_subspace_dim: "Berlekamp_subspace.dim = card P"
  using Berlekamp_subspace_eq_dim_vec RV.dim_is_n by simp

corollary card_berlekamp_basis_number_factors: "card (set (berlekamp_basis u)) = card P"
  unfolding Berlekamp_subspace_dim[symmetric]
  by (rule Berlekamp_subspace.dim_basis[symmetric], auto simp add: berlekamp_basis_basis)


lemma length_berlekamp_basis_numbers_factors: "length (berlekamp_basis u) = card P"
  using card_set_berlekamp_basis card_berlekamp_basis_number_factors by auto


end
end
end
end

context
  assumes "SORT_CONSTRAINT('a :: prime_card)"
begin

context
  fixes f :: "'a mod_ring poly" and n
  assumes sf: "square_free f"
  and n: "n = length (berlekamp_basis f)"
  and monic_f: "monic f"
begin
lemma berlekamp_basis_length_factorization: assumes f: "f = prod_list us"
  and d: "\<And> u. u \<in> set us \<Longrightarrow> degree u > 0"
  shows "length us \<le> n"
proof (cases "degree f = 0")
  case True
  have "us = []"
  proof (rule ccontr)
    assume "us \<noteq> []"
    from this obtain u where u: "u \<in> set us" by fastforce
    hence deg_u: "degree u > 0" using d by auto
    have "degree f = degree (prod_list us)" unfolding f ..
    also have "... = sum_list (map degree us)"
    proof (rule degree_prod_list_eq)
      fix p assume p: "p \<in> set us"
      show "p \<noteq> 0" using d[OF p] degree_0 by auto
    qed
    also have " ... \<ge> degree u" by (simp add: member_le_sum_list u)
    finally have "degree f > 0" using deg_u by auto
    thus False using True by auto
  qed
  thus ?thesis by simp
next
  case False
  hence f_not_0: "f \<noteq> 0" using degree_0 by fastforce
  obtain P where fin_P: "finite P" and f_P: "f = \<Prod>P" and P: "P \<subseteq> {p. irreducible p \<and> monic p}"
    using monic_square_free_irreducible_factorization[OF monic_f sf] by auto
  have n_card_P: "n = card P"
    using P False f_P fin_P length_berlekamp_basis_numbers_factors n by blast
  have distinct_us: "distinct us" using d f sf square_free_prod_list_distinct by blast
  let ?us'="(map normalize us)"
  have distinct_us': "distinct ?us'"
  proof (auto simp add: distinct_map)
    show "distinct us" by (rule distinct_us)
    show "inj_on normalize (set us)"
    proof (auto simp add: inj_on_def, rule ccontr)
       fix x y assume x: "x \<in> set us" and y: "y \<in> set us" and n: "normalize x = normalize y"
       and x_not_y: "x \<noteq> y"
       from normalize_eq_imp_smult[OF n]
       obtain c where c0: "c \<noteq> 0" and y_smult: "y = smult c x" by blast
       have sf_xy: "square_free (x*y)"
       proof (rule square_free_factor[OF _ sf])
          have "x*y = prod_list [x,y]" by simp
          also have "... dvd prod_list us"
            by (rule prod_list_dvd_prod_list_subset, auto simp add: x y x_not_y distinct_us)
          also have "... = f" unfolding f ..
          finally show "x * y dvd f" .
       qed
       have "x * y = smult c (x*x)" using y_smult mult_smult_right by auto
       hence sf_smult: "square_free (smult c (x*x))" using sf_xy by auto
       have "x*x dvd (smult c (x*x))" by (simp add: dvd_smult)
       hence "\<not> square_free (smult c (x*x))"
        by (metis d square_free_def x)
       thus "False" using sf_smult by contradiction
    qed
  qed
  have length_us_us': "length us = length ?us'" by simp
  have f_us': "f = prod_list ?us'"
  proof -
    have "f = normalize f" using monic_f f_not_0 by (simp add: normalize_monic)
    also have "... = prod_list ?us'" by (unfold f, rule prod_list_normalize[of us])
    finally show ?thesis .
  qed
  have "\<exists>Q. prod_list Q = prod_list ?us' \<and> length ?us' \<le> length Q
           \<and> (\<forall>u. u \<in> set Q \<longrightarrow> irreducible u \<and> monic u)"
  proof (rule exists_factorization_prod_list)
    show "degree (prod_list ?us') > 0" using False f_us' by auto
    show "square_free (prod_list ?us')" using f_us' sf by auto
    fix u assume u: "u \<in> set ?us'"
    have u_not0: "u \<noteq> 0" using d u degree_0 by fastforce
    have "degree u > 0" using d u by auto
    moreover have "monic u" using u monic_normalize[OF u_not0] by auto
    ultimately show "degree u > 0 \<and> monic u" by simp
  qed
  from this obtain Q
  where Q_us': "prod_list Q = prod_list ?us'"
  and length_us'_Q: "length ?us' \<le> length Q"
  and Q: "(\<forall>u. u \<in> set Q \<longrightarrow> irreducible u \<and> monic u)"
  by blast
  have distinct_Q: "distinct Q"
  proof (rule square_free_prod_list_distinct)
    show "square_free (prod_list Q)" using Q_us' f_us' sf by auto
    show "\<And>u. u \<in> set Q \<Longrightarrow> degree u > 0" using Q irreducible_degree_field by auto
  qed
  have set_Q_P: "set Q = P"
  proof (rule monic_factorization_uniqueness)
    show "\<Prod>(set Q) = \<Prod>P" using Q_us'
      by (metis distinct_Q f_P f_us' list.map_ident prod.distinct_set_conv_list)
  qed (insert P Q fin_P, auto)
  hence "length Q = card P" using distinct_Q distinct_card by fastforce
  have "length us = length ?us'" by (rule length_us_us')
  also have "... \<le> length Q" using length_us'_Q by auto
  also have "... = card (set Q)" using distinct_card[OF distinct_Q] by simp
  also have "... = card P" using set_Q_P by simp
  finally show ?thesis using n_card_P by simp
qed

lemma berlekamp_basis_irreducible: assumes f: "f = prod_list us"
  and n_us: "length us = n"
  and us: "\<And> u. u \<in> set us \<Longrightarrow> degree u > 0"
  and u: "u \<in> set us"
  shows "irreducible u"
proof (fold irreducible_connect_field, intro irreducible\<^sub>dI[OF us[OF u]])
  fix q r :: "'a mod_ring poly"
  assume dq: "degree q > 0" and qu: "degree q < degree u" and dr: "degree r > 0" and uqr: "u = q * r"
  with us[OF u] have q: "q \<noteq> 0" and r: "r \<noteq> 0" by auto
  from split_list[OF u] obtain xs ys where id: "us = xs @ u # ys" by auto
  let ?us = "xs @ q # r # ys"
  have f: "f = prod_list ?us" unfolding f id uqr by simp
  {
    fix x
    assume "x \<in> set ?us"
    with us[unfolded id] dr dq have "degree x > 0" by auto
  }
  from berlekamp_basis_length_factorization[OF f this]
  have "length ?us \<le> n" by simp
  also have "\<dots> = length us" unfolding n_us by simp
  also have "\<dots> < length ?us" unfolding id by simp
  finally show False by simp
qed
end

lemma not_irreducible_factor_yields_prime_factors:
  assumes uf: "u dvd (f :: 'b :: {field_gcd} poly)" and fin: "finite P"
      and fP: "f = \<Prod>P" and P: "P \<subseteq> {q. irreducible q \<and> monic q}"
    and u: "degree u > 0" "\<not> irreducible u"
  shows "\<exists> pi pj. pi \<in> P \<and> pj \<in> P \<and> pi \<noteq> pj \<and> pi dvd u \<and> pj dvd u"
proof -
  from finite_distinct_list[OF fin] obtain ps where Pps: "P = set ps" and dist: "distinct ps" by auto
  have fP: "f = prod_list ps" unfolding fP Pps using dist
    by (simp add: prod.distinct_set_conv_list)
  note P = P[unfolded Pps]
  have "set ps \<subseteq> P" unfolding Pps by auto
  from uf[unfolded fP] P dist this
  show ?thesis
  proof (induct ps)
    case Nil
    with u show ?case using divides_degree[of u 1] by auto
  next
    case (Cons p ps)
    from Cons(3) have ps: "set ps \<subseteq> {q. irreducible q \<and> monic q}" by auto
    from Cons(2) have dvd: "u dvd p * prod_list ps" by simp
    obtain k where gcd: "u = gcd p u * k" by (meson dvd_def gcd_dvd2)
    from Cons(3) have *: "monic p" "irreducible p" "p \<noteq> 0" by auto
    from monic_irreducible_gcd[OF *(1), of u] *(2)
    have "gcd p u = 1 \<or> gcd p u = p" by auto
    thus ?case
    proof
      assume "gcd p u = 1"
      then have "Rings.coprime p u"
        by (rule gcd_eq_1_imp_coprime)
      with dvd have "u dvd prod_list ps"
        using coprime_dvd_mult_right_iff coprime_imp_coprime by blast
      from Cons(1)[OF this ps] Cons(4-5) show ?thesis by auto
    next
      assume "gcd p u = p"
      with gcd have upk: "u = p * k" by auto
      hence p: "p dvd u" by auto
      from dvd[unfolded upk] *(3) have kps: "k dvd prod_list ps" by auto
      from dvd u * have dk: "degree k > 0"
        by (metis gr0I irreducible_mult_unit_right is_unit_iff_degree mult_zero_right upk)
      from ps kps have "\<exists> q \<in> set ps. q dvd k"
      proof (induct ps)
        case Nil
        with dk show ?case using divides_degree[of k 1] by auto
      next
        case (Cons p ps)
        from Cons(3) have dvd: "k dvd p * prod_list ps" by simp
        obtain l where gcd: "k = gcd p k * l" by (meson dvd_def gcd_dvd2)
        from Cons(2) have *: "monic p" "irreducible p" "p \<noteq> 0" by auto
        from monic_irreducible_gcd[OF *(1), of k] *(2)
        have "gcd p k = 1 \<or> gcd p k = p" by auto
        thus ?case
        proof
          assume "gcd p k = 1"
          with dvd have "k dvd prod_list ps"
            by (metis dvd_triv_left gcd_greatest_mult mult.left_neutral)
          from Cons(1)[OF _ this] Cons(2) show ?thesis by auto
        next
          assume "gcd p k = p"
          with gcd have upk: "k = p * l" by auto
          hence p: "p dvd k" by auto
          thus ?thesis by auto
        qed
      qed
      then obtain q where q: "q \<in> set ps" and dvd: "q dvd k" by auto
      from dvd upk have qu: "q dvd u" by auto
      from Cons(4) q have "p \<noteq> q" by auto
      thus ?thesis using q p qu Cons(5) by auto
    qed
  qed
qed

lemma berlekamp_factorization_main:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and vs: "vs = vs1 @ vs2"
    and vsf: "vs = berlekamp_basis f"
    and n_bb: "n = length (berlekamp_basis f)"
    and n: "n = length us1 + n2"
    and us: "us = us1 @ berlekamp_factorization_main d divs vs2 n2"
    and us1: "\<And> u. u \<in> set us1 \<Longrightarrow> monic u \<and> irreducible u"
    and divs: "\<And> d. d \<in> set divs \<Longrightarrow> monic d \<and> degree d > 0"
    and vs1: "\<And> u v i. v \<in> set vs1 \<Longrightarrow> u \<in> set us1 \<union> set divs
      \<Longrightarrow> i < CARD('a) \<Longrightarrow> gcd u (v - [:of_nat i:]) \<in> {1,u}"
    and f: "f = prod_list (us1 @ divs)"
    and deg_f: "degree f > 0"
    and d: "\<And> g. g dvd f \<Longrightarrow> degree g = d \<Longrightarrow> irreducible g" 
  shows "f = prod_list us \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)"
proof -
  have mon_f: "monic f" unfolding f
    by (rule monic_prod_list, insert divs us1, auto)
  from monic_square_free_irreducible_factorization[OF mon_f sf_f] obtain P where
    P: "finite P" "f = \<Prod> P" "P \<subseteq> {q. irreducible q \<and> monic q}" by auto
  hence f0: "f \<noteq> 0" by auto
  show ?thesis
    using vs n us divs f us1 vs1
  proof (induct vs2 arbitrary: divs n2 us1 vs1)
    case (Cons v vs2)
    show ?case
    proof (cases "v = 1")
      case False
      from Cons(2) vsf have v: "v \<in> set (berlekamp_basis f)" by auto
      from berlekamp_basis_eq_8[OF this] have vf: "[v ^ CARD('a) = v] (mod f)" .
      let ?gcd = "\<lambda> u i. gcd u (v - [:of_int i:])"
      let ?gcdn = "\<lambda> u i. gcd u (v - [:of_nat i:])"
      let ?map = "\<lambda> u. (map (\<lambda> i. ?gcd u i) [0 ..< CARD('a)])"
      define udivs where "udivs \<equiv> \<lambda> u. filter (\<lambda> w. w \<noteq> 1) (?map u)"
      {
        obtain xs where xs: "[0..<CARD('a)] = xs" by auto
        have "udivs = (\<lambda> u. [w. i \<leftarrow> [0 ..< CARD('a)], w \<leftarrow> [?gcd u i], w \<noteq> 1])"
          unfolding udivs_def xs
          by (intro ext, auto simp: o_def, induct xs, auto)
      } note udivs_def' = this
      define facts where "facts \<equiv> [ w . u \<leftarrow> divs, w \<leftarrow> udivs u]"
      {
        fix u
        assume u: "u \<in> set divs"
        then obtain bef aft where divs: "divs = bef @ u # aft" by (meson split_list)
        from Cons(5)[OF u] have mon_u: "monic u" by simp
        have uf: "u dvd f" unfolding Cons(6) divs by auto
        from vf uf have vu: "[v ^ CARD('a) = v] (mod u)" by (rule cong_dvd_modulus_poly)
        from square_free_factor[OF uf sf_f] have sf_u: "square_free u" .
        let ?g = "?gcd u"
        from mon_u have u0: "u \<noteq> 0" by auto
        have "u = (\<Prod>c\<in>UNIV. gcd u (v - [:c:]))"
          using Berlekamp_gcd_step[OF vu mon_u sf_u] .
        also have "\<dots> = (\<Prod>i \<in> {0..< int CARD('a)}. ?g i)"
          by (rule sym, rule prod.reindex_cong[OF to_int_mod_ring_hom.inj_f range_to_int_mod_ring[symmetric]],
          simp add: of_int_of_int_mod_ring)
        finally have u_prod: "u = (\<Prod>i \<in> {0..< int CARD('a)}. ?g i)" .
        let ?S = "{0..<int CARD('a)} - {i. ?g i = 1}"
        {
          fix i
          assume "i \<in> ?S"
          hence "?g i \<noteq> 1" by auto
          moreover have mgi: "monic (?g i)" by (rule poly_gcd_monic, insert u0, auto)
          ultimately have "degree (?g i) > 0"
            using monic_degree_0 by blast
          note this mgi
        } note gS = this

        have int_set: "int ` set [0..<CARD('a)] = {0 ..< int CARD('a)}"
          by (simp add: image_int_atLeastLessThan)

        have inj: "inj_on ?g ?S" unfolding inj_on_def
        proof (intro ballI impI)
          fix i j
          assume i: "i \<in> ?S" and j: "j \<in> ?S" and gij: "?g i = ?g j"
          show "i = j"
          proof (rule ccontr)
            define S where "S = {0..<int CARD('a)} - {i,j}"
            have id: "{0..<int CARD('a)} = (insert i (insert j S))" and S: "i \<notin> S" "j \<notin> S" "finite S"
              using i j unfolding S_def by auto
            assume ij: "i \<noteq> j"
            have "u = (\<Prod>i \<in> {0..< int CARD('a)}. ?g i)" by fact
            also have "\<dots> = ?g i * ?g j * (\<Prod>i \<in> S. ?g i)"
              unfolding id using S ij by auto
            also have "\<dots> = ?g i * ?g i * (\<Prod>i \<in> S. ?g i)" unfolding gij by simp
            finally have dvd: "?g i * ?g i dvd u" unfolding dvd_def by auto
            with sf_u[unfolded square_free_def, THEN conjunct2, rule_format, OF gS(1)[OF i]]
            show False by simp
          qed
        qed

        have "u = (\<Prod>i \<in> {0..< int CARD('a)}. ?g i)" by fact
        also have "\<dots> = (\<Prod>i \<in> ?S. ?g i)"
          by (rule sym, rule prod.setdiff_irrelevant, auto)
        also have "\<dots> = \<Prod> (set (udivs u))" unfolding udivs_def set_filter set_map
          by (rule sym, rule prod.reindex_cong[of ?g, OF inj _ refl], auto simp: int_set[symmetric])
        finally have u_udivs: "u = \<Prod>(set (udivs u))" .
        {
          fix w
          assume mem: "w \<in> set (udivs u)"
          then obtain i where w: "w = ?g i" and i: "i \<in> ?S"
            unfolding udivs_def set_filter set_map int_set by auto
          have wu: "w dvd u" by (simp add: w)
          let ?v = "\<lambda> j. v - [:of_nat j:]"
          define j where "j = nat i"
          from i have j: "of_int i = (of_nat j :: 'a mod_ring)" "j < CARD('a)" unfolding j_def by auto
          from gS[OF i, folded w] have *: "degree w > 0" "monic w" "w \<noteq> 0" by auto
          from w have "w dvd ?v j" using j by simp
          hence gcdj: "?gcdn w j = w" by (metis gcd.commute gcd_left_idem j(1) w)
          {
            fix j'
            assume j': "j' < CARD('a)"
            have "?gcdn w j' \<in> {1,w}"
            proof (rule ccontr)
              assume not: "?gcdn w j' \<notin> {1,w}"
              with gcdj have neq: "int j' \<noteq> int j" by auto
              (* next step will yield contradiction to square_free u *)
              let ?h = "?gcdn w j'"
              from *(3) not have deg: "degree ?h > 0"
                using monic_degree_0 poly_gcd_monic by auto
              have hw: "?h dvd w" by auto
              have "?h dvd ?gcdn u j'" using wu using dvd_trans by auto
              also have "?gcdn u j' = ?g j'" by simp
              finally have hj': "?h dvd ?g j'" by auto
              from divides_degree[OF this] deg u0 have degj': "degree (?g j') > 0" by auto
              hence j'1: "?g j' \<noteq> 1" by auto
              with j' have mem': "?g j' \<in> set (udivs u)" unfolding udivs_def by auto
              from degj' j' have j'S: "int j' \<in> ?S" by auto
              from i j have jS: "int j \<in> ?S" by auto
              from inj_on_contraD[OF inj neq j'S jS]
              have neq: "w \<noteq> ?g j'" using w j by auto
              have cop: "\<not> coprime w (?g j')" using hj' hw deg
                by (metis coprime_not_unit_not_dvd poly_dvd_1 Nat.neq0_conv)
              obtain w' where w': "?g j' = w'" by auto
              from u_udivs sf_u have "square_free (\<Prod>(set (udivs u)))" by simp
              from square_free_prodD[OF this finite_set mem mem'] cop neq
              show False by simp
            qed
          }
          from gS[OF i, folded w] i this
          have "degree w > 0" "monic w" "\<And> j. j < CARD('a) \<Longrightarrow> ?gcdn w j \<in> {1,w}" by auto
        } note udivs = this
        let ?is = "filter (\<lambda> i. ?g i \<noteq> 1) (map int [0 ..< CARD('a)])"
        have id: "udivs u = map ?g ?is"
          unfolding udivs_def filter_map o_def ..
        have dist: "distinct (udivs u)" unfolding id distinct_map
        proof (rule conjI[OF distinct_filter], unfold distinct_map)
          have "?S = set ?is" unfolding int_set[symmetric] by auto
          thus "inj_on ?g (set ?is)" using inj by auto
        qed (auto simp: inj_on_def)
        from u_udivs prod.distinct_set_conv_list[OF dist, of id]
        have "prod_list (udivs u) = u" by auto
        note udivs this dist
      } note udivs = this
      have facts: "facts = concat (map udivs divs)"
        unfolding facts_def by auto
      obtain lin nonlin where part: "List.partition (\<lambda> q. degree q = d) facts = (lin,nonlin)" 
        by force
      from Cons(6) have "f = prod_list us1 * prod_list divs" by auto
      also have "prod_list divs = prod_list facts" unfolding facts using udivs(4)
        by (induct divs, auto)
      finally have f: "f = prod_list us1 * prod_list facts" .
      note facts' = facts
      {
        fix u
        assume u: "u \<in> set facts"
        from u[unfolded facts] obtain u' where u': "u' \<in> set divs" and u: "u \<in> set (udivs u')" by auto
        from u' udivs(1-2)[OF u' u] prod_list_dvd[OF u, unfolded udivs(4)[OF u']]
        have "degree u > 0" "monic u" "\<exists> u' \<in> set divs. u dvd u'" by auto
      } note facts = this
      have not1: "(v = 1) = False" using False by auto
      have "us = us1 @ (if length divs = n2 then divs
          else let (lin, nonlin) = List.partition (\<lambda>q. degree q = d) facts
               in lin @ berlekamp_factorization_main d nonlin vs2 (n2 - length lin))"
        unfolding Cons(4) facts_def udivs_def' berlekamp_factorization_main.simps Let_def not1 if_False
        by (rule arg_cong[where f = "\<lambda> x. us1 @ x"], rule if_cong, simp_all) (* takes time *)
      hence res: "us = us1 @ (if length divs = n2 then divs else
               lin @ berlekamp_factorization_main d nonlin vs2 (n2 - length lin))"
        unfolding part by auto
      show ?thesis
      proof (cases "length divs = n2")
        case False
        with res have us: "us = (us1 @ lin) @ berlekamp_factorization_main d nonlin vs2 (n2 - length lin)"
          by auto
        from Cons(2) have vs: "vs = (vs1 @ [v]) @ vs2" by auto
        have f: "f = prod_list ((us1 @ lin) @ nonlin)"
          unfolding f using prod_list_partition[OF part] by simp
        {
          fix u
          assume "u \<in> set ((us1 @ lin) @ nonlin)"
          with part have "u \<in> set facts \<union> set us1" by auto
          with facts Cons(7) have "degree u > 0" by (auto simp: irreducible_degree_field)
        } note deg = this
        from berlekamp_basis_length_factorization[OF sf_f n_bb mon_f f deg, unfolded Cons(3)]
        have "n2 \<ge> length lin" by auto
        hence n: "n = length (us1 @ lin) + (n2 - length lin)"
          unfolding Cons(3) by auto
        show ?thesis
        proof (rule Cons(1)[OF vs n us _ f])
          fix u
          assume "u \<in> set nonlin"
          with part have "u \<in> set facts" by auto
          from facts[OF this] show "monic u \<and> degree u > 0" by auto
        next
          fix u
          assume u: "u \<in> set (us1 @ lin)"
          {
            assume *: "\<not> (monic u \<and> irreducible\<^sub>d u)"
            with Cons(7) u have "u \<in> set lin" by auto
            with part have uf: "u \<in> set facts" and deg: "degree u = d" by auto
            from facts[OF uf] obtain u' where "u' \<in> set divs" and uu': "u dvd u'" by auto
            from this(1) have "u' dvd f" unfolding Cons(6) using prod_list_dvd[of u'] by auto
            with uu' have "u dvd f" by (rule dvd_trans)
            from facts[OF uf] d[OF this deg] * have False by auto
          }
          thus "monic u \<and> irreducible u" by auto
        next
          fix w u i
          assume w: "w \<in> set (vs1 @ [v])"
            and u: "u \<in> set (us1 @ lin) \<union> set nonlin"
            and i: "i < CARD('a)"
          from u part have u: "u \<in> set us1 \<union> set facts" by auto
          show "gcd u (w - [:of_nat i:]) \<in> {1, u}"
          proof (cases "u \<in> set us1")
            case True
            from Cons(7)[OF this] have "monic u" "irreducible u" by auto
            thus ?thesis by (rule monic_irreducible_gcd)
          next
            case False
            with u have u: "u \<in> set facts" by auto
            show ?thesis
            proof (cases "w = v")
              case True
              from u[unfolded facts'] obtain u' where u: "u \<in> set (udivs u')"
                and u': "u' \<in> set divs" by auto
              from udivs(3)[OF u' u i] show ?thesis unfolding True .
            next
              case False
              with w have w: "w \<in> set vs1" by auto
              from u obtain u' where u': "u' \<in> set divs" and dvd: "u dvd u'"
                using facts(3)[of u] dvd_refl[of u] by blast
              from w have "w \<in> set vs1 \<or> w = v" by auto
              from facts(1-2)[OF u] have u: "monic u" by auto
              from Cons(8)[OF w _ i] u'
              have "gcd u' (w - [:of_nat i:]) \<in> {1, u'}" by auto
              with dvd u show ?thesis by (rule monic_gcd_dvd)
            qed
          qed
        qed
      next
        case True
        with res have us: "us = us1 @ divs" by auto
        from Cons(3) True have n: "n = length us" unfolding us by auto
        show ?thesis unfolding us[symmetric]
        proof (intro conjI ballI)
          show f: "f = prod_list us" unfolding us using Cons(6) by simp
          {
            fix u
            assume "u \<in> set us"
            hence "degree u > 0" using Cons(5) Cons(7)[unfolded irreducible\<^sub>d_def]
              unfolding us by (auto simp: irreducible_degree_field)
          } note deg = this
          fix u
          assume u: "u \<in> set us"
          thus "monic u" unfolding us using Cons(5) Cons(7) by auto
          show "irreducible u"
            by (rule berlekamp_basis_irreducible[OF sf_f n_bb mon_f f n[symmetric] deg u])
        qed
      qed
    next
      case True (* v = 1 *)
      with Cons(4) have us: "us = us1 @ berlekamp_factorization_main d divs vs2 n2" by simp
      from Cons(2) True have vs: "vs = (vs1 @ [1]) @ vs2" by auto
      show ?thesis
      proof (rule Cons(1)[OF vs Cons(3) us Cons(5-7)], goal_cases)
        case (3 v u i)
        show ?case
        proof (cases "v = 1")
          case False
          with 3 Cons(8)[of v u i] show ?thesis by auto
        next
          case True
          hence deg: "degree (v - [: of_nat i :]) = 0"
            by (metis (no_types, hide_lams) degree_pCons_0 diff_pCons diff_zero pCons_one)
          from 3(2) Cons(5,7)[of u] have "monic u" by auto
          from gcd_monic_constant[OF this deg] show ?thesis .
        qed
      qed
    qed
  next
    case Nil
    with vsf have vs1: "vs1 = berlekamp_basis f" by auto
    from Nil(3) have us: "us = us1 @ divs" by auto
    from Nil(4,6) have md: "\<And> u. u \<in> set us \<Longrightarrow> monic u \<and> degree u > 0"
      unfolding us by (auto simp: irreducible_degree_field)
    from Nil(7)[unfolded vs1] us
    have no_further_splitting_possible:
      "\<And> u v i. v \<in> set (berlekamp_basis f) \<Longrightarrow> u \<in> set us
      \<Longrightarrow> i < CARD('a) \<Longrightarrow> gcd u (v - [:of_nat i:]) \<in> {1, u}" by auto
    from Nil(5) us have prod: "f = prod_list us" by simp
    show ?case
    proof (intro conjI ballI)
      fix u
      assume u: "u \<in> set us"
      from md[OF this] have mon_u: "monic u" and deg_u: "degree u > 0" by auto
      from prod u have uf: "u dvd f" by (simp add: prod_list_dvd)
      from monic_square_free_irreducible_factorization[OF mon_f sf_f] obtain P where
        P: "finite P" "f = \<Prod>P" "P \<subseteq> {q. irreducible q \<and> monic q}" by auto
      show "irreducible u"
      proof (rule ccontr)
        assume irr_u: "\<not> irreducible u"
        from not_irreducible_factor_yields_prime_factors[OF uf P deg_u this]
        obtain pi pj where pij: "pi \<in> P" "pj \<in> P" "pi \<noteq> pj" "pi dvd u" "pj dvd u" by blast
        from exists_vector_in_Berlekamp_basis_dvd[OF
          deg_f berlekamp_basis_basis[OF deg_f, folded vs1] finite_set
          P pij(1-3) mon_f sf_f irr_u uf mon_u pij(4-5), unfolded vs1]
        obtain v s where v: "v \<in> set (berlekamp_basis f)" 
          and gcd: "gcd u (v - [:s:]) \<notin> {1,u}" using is_unit_gcd by auto
        from surj_of_nat_mod_ring[of s] obtain i where i: "i < CARD('a)" and s: "s = of_nat i" by auto
        from no_further_splitting_possible[OF v u i] gcd[unfolded s]
        show False by auto
      qed
    qed (insert prod md, auto)
  qed
qed

lemma berlekamp_monic_factorization:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and us: "berlekamp_monic_factorization d f = us"
    and d: "\<And> g. g dvd f \<Longrightarrow> degree g = d \<Longrightarrow> irreducible g" 
    and deg: "degree f > 0" 
    and mon: "monic f" 
  shows "f = prod_list us \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)"
proof -
  from us[unfolded berlekamp_monic_factorization_def Let_def] deg
  have us: "us = [] @ berlekamp_factorization_main d [f] (berlekamp_basis f) (length (berlekamp_basis f))"
    by (auto)
  have id: "berlekamp_basis f = [] @ berlekamp_basis f"
    "length (berlekamp_basis f) = length [] + length (berlekamp_basis f)"
    "f = prod_list ([] @ [f])"
    by auto
  show "f = prod_list us \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)"
    by (rule berlekamp_factorization_main[OF sf_f id(1) refl refl id(2) us _ _ _ id(3)],
    insert mon deg d, auto)
qed
end

end
