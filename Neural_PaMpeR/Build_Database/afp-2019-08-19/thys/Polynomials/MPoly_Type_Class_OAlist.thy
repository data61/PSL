(* Author: Fabian Immler, TU Muenchen *)
(* Author: Florian Haftmann, TU Muenchen *)
(* Author: Andreas Lochbihler, ETH Zurich *)
(* Author: Alexander Maletzky, RISC Linz *)

section \<open>Executable Representation of Polynomial Mappings as Association Lists\<close>

theory MPoly_Type_Class_OAlist
  imports Term_Order
begin

instantiation pp :: (type, "{equal, zero}") equal
begin

definition equal_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool" where
  "equal_pp p q \<equiv> (\<forall>t. lookup_pp p t = lookup_pp q t)"

instance by standard (auto simp: equal_pp_def intro: pp_eqI)

end

instantiation poly_mapping :: (type, "{equal, zero}") equal
begin

definition equal_poly_mapping :: "('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" where
  equal_poly_mapping_def [code del]: "equal_poly_mapping p q \<equiv> (\<forall>t. lookup p t = lookup q t)"

instance by standard (auto simp: equal_poly_mapping_def intro: poly_mapping_eqI)

end

subsection \<open>Power-Products Represented by @{type oalist_tc}\<close>

definition PP_oalist :: "('a::linorder, 'b::zero) oalist_tc \<Rightarrow> ('a, 'b) pp"
  where "PP_oalist xs = pp_of_fun (OAlist_tc_lookup xs)"

code_datatype PP_oalist

lemma lookup_PP_oalist [simp, code]: "lookup_pp (PP_oalist xs) = OAlist_tc_lookup xs"
  unfolding PP_oalist_def
proof (rule lookup_pp_of_fun)
  have "{x. OAlist_tc_lookup xs x \<noteq> 0} \<subseteq> fst ` set (list_of_oalist_tc xs)"
  proof (rule, simp)
    fix x
    assume "OAlist_tc_lookup xs x \<noteq> 0"
    thus "x \<in> fst ` set (list_of_oalist_tc xs)"
      using in_OAlist_tc_sorted_domain_iff_lookup set_OAlist_tc_sorted_domain by blast
  qed
  also have "finite ..." by simp
  finally (finite_subset) show "finite {x. OAlist_tc_lookup xs x \<noteq> 0}" .
qed

lemma keys_PP_oalist [code]: "keys_pp (PP_oalist xs) = set (OAlist_tc_sorted_domain xs)"
  by (rule set_eqI, simp add: keys_pp_iff in_OAlist_tc_sorted_domain_iff_lookup)

lemma lex_comp_PP_oalist [code]:
  "lex_comp' (PP_oalist xs) (PP_oalist ys) =
         the (OAlist_tc_lex_ord (\<lambda>_ x y. Some (comparator_of x y)) xs ys)"
  for xs ys::"('a::nat, 'b::nat) oalist_tc"
proof (cases "lex_comp' (PP_oalist xs) (PP_oalist ys) = Eq")
  case True
  hence "PP_oalist xs = PP_oalist ys" by (rule lex_comp'_EqD)
  hence eq: "OAlist_tc_lookup xs = OAlist_tc_lookup ys" by (simp add: pp_eq_iff)
  have "OAlist_tc_lex_ord (\<lambda>_ x y. Some (comparator_of x y)) xs ys = Some Eq"
    by (rule OAlist_tc_lex_ord_EqI, simp add: eq)
  thus ?thesis by (simp add: True)
next
  case False
  then obtain x where 1: "x \<in> keys_pp (rep_nat_pp (PP_oalist xs)) \<union> keys_pp (rep_nat_pp (PP_oalist ys))"
    and 2: "comparator_of (lookup_pp (rep_nat_pp (PP_oalist xs)) x) (lookup_pp (rep_nat_pp (PP_oalist ys)) x) =
          lex_comp' (PP_oalist xs) (PP_oalist ys)"
    and 3: "\<And>y. y < x \<Longrightarrow> lookup_pp (rep_nat_pp (PP_oalist xs)) y = lookup_pp (rep_nat_pp (PP_oalist ys)) y"
    by (rule lex_comp'_valE, blast)
  have "OAlist_tc_lex_ord (\<lambda>_ x y. Some (comparator_of x y)) xs ys = Some (lex_comp' (PP_oalist xs) (PP_oalist ys))"
  proof (rule OAlist_tc_lex_ord_valI)
    from False show "Some (lex_comp' (PP_oalist xs) (PP_oalist ys)) \<noteq> Some Eq" by simp
  next
    from 1 have "abs_nat x \<in> abs_nat ` (keys_pp (rep_nat_pp (PP_oalist xs)) \<union> keys_pp (rep_nat_pp (PP_oalist ys)))"
      by (rule imageI)
    also have "... = fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)"
      by (simp add: keys_rep_nat_pp_pp keys_PP_oalist OAlist_tc_sorted_domain_def image_Un image_image)
    finally show "abs_nat x \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)" .
  next
    show "Some (lex_comp' (PP_oalist xs) (PP_oalist ys)) =
          Some (comparator_of (OAlist_tc_lookup xs (abs_nat x)) (OAlist_tc_lookup ys (abs_nat x)))"
      by (simp add: 2[symmetric] lookup_rep_nat_pp_pp)
  next
    fix y::'a
    assume "y < abs_nat x"
    hence "rep_nat y < x" by (metis abs_inverse ord_iff(2))
    hence "lookup_pp (rep_nat_pp (PP_oalist xs)) (rep_nat y) = lookup_pp (rep_nat_pp (PP_oalist ys)) (rep_nat y)"
      by (rule 3)
    hence "OAlist_tc_lookup xs y = OAlist_tc_lookup ys y" by (auto simp: lookup_rep_nat_pp_pp elim: rep_inj)
    thus "Some (comparator_of (OAlist_tc_lookup xs y) (OAlist_tc_lookup ys y)) = Some Eq" by simp
  qed
  thus ?thesis by simp
qed

lemma zero_PP_oalist [code]: "(0::('a::linorder, 'b::zero) pp) = PP_oalist OAlist_tc_empty"
  by (rule pp_eqI, simp add: lookup_OAlist_tc_empty)

lemma plus_PP_oalist [code]:
  "PP_oalist xs + PP_oalist ys = PP_oalist (OAlist_tc_map2_val_neutr (\<lambda>_. (+)) xs ys)"
  by (rule pp_eqI, simp add: lookup_plus_pp, rule lookup_OAlist_tc_map2_val_neutr[symmetric], simp_all)

lemma minus_PP_oalist [code]:
  "PP_oalist xs - PP_oalist ys = PP_oalist (OAlist_tc_map2_val_rneutr (\<lambda>_. (-)) xs ys)"
  by (rule pp_eqI, simp add: lookup_minus_pp, rule lookup_OAlist_tc_map2_val_rneutr[symmetric], simp)

lemma equal_PP_oalist [code]: "equal_class.equal (PP_oalist xs) (PP_oalist ys) = (xs = ys)"
  by (simp add: equal_eq pp_eq_iff, auto elim: OAlist_tc_lookup_inj)

lemma lcs_PP_oalist [code]:
  "lcs (PP_oalist xs) (PP_oalist ys) = PP_oalist (OAlist_tc_map2_val_neutr (\<lambda>_. max) xs ys)"
  for xs ys :: "('a::linorder, 'b::add_linorder_min) oalist_tc"
  by (rule pp_eqI, simp add: lookup_lcs_pp, rule lookup_OAlist_tc_map2_val_neutr[symmetric], simp_all add: max_def)

lemma deg_pp_PP_oalist [code]: "deg_pp (PP_oalist xs) = sum_list (map snd (list_of_oalist_tc xs))"
proof -
  have "irreflp ((<)::_::linorder \<Rightarrow> _)" by (rule irreflpI, simp)
  have "deg_pp (PP_oalist xs) = sum (OAlist_tc_lookup xs) (set (OAlist_tc_sorted_domain xs))"
    by (simp add: deg_pp_alt keys_PP_oalist)
  also have "... = sum_list (map (OAlist_tc_lookup xs) (OAlist_tc_sorted_domain xs))"
    by (rule sum.distinct_set_conv_list, rule distinct_sorted_wrt_irrefl,
        fact, fact transp_less, fact sorted_OAlist_tc_sorted_domain)
  also have "... = sum_list (map snd (list_of_oalist_tc xs))"
    by (rule arg_cong[where f=sum_list], simp add: OAlist_tc_sorted_domain_def OAlist_tc_lookup_eq_valueI)
  finally show ?thesis .
qed

lemma single_PP_oalist [code]: "single_pp x e = PP_oalist (oalist_tc_of_list [(x, e)])"
  by (rule pp_eqI, simp add: lookup_single_pp OAlist_tc_lookup_single)

definition adds_pp_add_linorder :: "('b, 'a::add_linorder) pp \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pp_add_linorder = (adds)"

lemma adds_pp_PP_oalist [code]:
  "adds_pp_add_linorder (PP_oalist xs) (PP_oalist ys) = OAlist_tc_prod_ord (\<lambda>_. less_eq) xs ys"
  for xs ys::"('a::linorder, 'b::add_linorder_min) oalist_tc"
proof (simp add: adds_pp_add_linorder_def adds_pp_iff adds_poly_mapping lookup_pp.rep_eq[symmetric] OAlist_tc_prod_ord_alt le_fun_def,
      intro iffI allI ballI)
  fix k
  assume "\<forall>x. OAlist_tc_lookup xs x \<le> OAlist_tc_lookup ys x"
  thus "OAlist_tc_lookup xs k \<le> OAlist_tc_lookup ys k" by blast
next
  fix x
  assume *: "\<forall>k\<in>fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys).
              OAlist_tc_lookup xs k \<le> OAlist_tc_lookup ys k"
  show "OAlist_tc_lookup xs x \<le> OAlist_tc_lookup ys x"
  proof (cases "x \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)")
    case True
    with * show ?thesis ..
  next
    case False
    hence "x \<notin> set (OAlist_tc_sorted_domain xs)" and "x \<notin> set (OAlist_tc_sorted_domain ys)"
      by (simp_all add: set_OAlist_tc_sorted_domain)
    thus ?thesis by (simp add: in_OAlist_tc_sorted_domain_iff_lookup)
  qed
qed

subsubsection \<open>Constructor\<close>

definition "sparse\<^sub>0 xs = PP_oalist (oalist_tc_of_list xs)" \<comment>\<open>sparse representation\<close>

subsubsection \<open>Computations\<close>

experiment begin

abbreviation "X \<equiv> 0::nat"
abbreviation "Y \<equiv> 1::nat"
abbreviation "Z \<equiv> 2::nat"

value [code] "sparse\<^sub>0 [(X, 2::nat), (Z, 7)]"

lemma
  "sparse\<^sub>0 [(X, 2::nat), (Z, 7)] - sparse\<^sub>0 [(X, 2), (Z, 2)] = sparse\<^sub>0 [(Z, 5)]"
  by eval

lemma
  "lcs (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 7)]) (sparse\<^sub>0 [(Y, 3), (Z, 2)]) = sparse\<^sub>0 [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(sparse\<^sub>0 [(X, 2::nat), (Z, 1)]) adds (sparse\<^sub>0 [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "lookup_pp (sparse\<^sub>0 [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

lemma
  "lex_comp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)]) = Lt"
  by eval

lemma
  "lex_comp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)], 3::nat) (sparse\<^sub>0 [(X, 4)], 2) = Lt"
  by eval

lemma
  "lex_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "lex_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "\<not> dlex_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "dlex_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)])"
  by eval

lemma
  "\<not> drlex_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)])"
  by eval

end

subsection \<open>\<open>MP_oalist\<close>\<close>

lift_definition MP_oalist :: "('a::nat_term, 'b::zero) oalist_ntm \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is OAlist_lookup_ntm
proof -
  fix xs :: "('a, 'b) oalist_ntm"
  have "{x. OAlist_lookup_ntm xs x \<noteq> 0} \<subseteq> fst ` set (fst (list_of_oalist_ntm xs))"
  proof (rule, simp)
    fix x
    assume "OAlist_lookup_ntm xs x \<noteq> 0"
    thus "x \<in> fst ` set (fst (list_of_oalist_ntm xs))"
      using oa_ntm.in_sorted_domain_iff_lookup oa_ntm.set_sorted_domain by blast
  qed
  also have "finite ..." by simp
  finally (finite_subset) show "finite {x. OAlist_lookup_ntm xs x \<noteq> 0}" .
qed

lemmas [simp, code] = MP_oalist.rep_eq

code_datatype MP_oalist

lemma keys_MP_oalist [code]: "keys (MP_oalist xs) = set (map fst (fst (list_of_oalist_ntm xs)))"
  by (rule set_eqI, simp add: in_keys_iff oa_ntm.in_sorted_domain_iff_lookup[simplified oa_ntm.set_sorted_domain])

lemma MP_oalist_empty [simp]: "MP_oalist (OAlist_empty_ntm ko) = 0"
  by (rule poly_mapping_eqI, simp add: oa_ntm.lookup_empty)

lemma zero_MP_oalist [code]: "(0::('a::{linorder,nat_term} \<Rightarrow>\<^sub>0 'b::zero)) = MP_oalist (OAlist_empty_ntm nat_term_order_of_le)"
  by simp

definition is_zero :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where [code_abbrev]: "is_zero p \<longleftrightarrow> (p = 0)"

lemma is_zero_MP_oalist [code]: "is_zero (MP_oalist xs) = List.null (fst (list_of_oalist_ntm xs))"
  unfolding is_zero_def List.null_def
proof
  assume "MP_oalist xs = 0"
  hence "OAlist_lookup_ntm xs k = 0" for k by (simp add: poly_mapping_eq_iff)
  thus "fst (list_of_oalist_ntm xs) = []"
    by (metis image_eqI ko_ntm.min_key_val_raw_in oa_ntm.in_sorted_domain_iff_lookup oa_ntm.set_sorted_domain)
next
  assume "fst (list_of_oalist_ntm xs) = []"
  hence "OAlist_lookup_ntm xs k = 0" for k
    by (metis oa_ntm.list_of_oalist_empty oa_ntm.lookup_empty oalist_ntm_eqI surjective_pairing)
  thus "MP_oalist xs = 0" by (simp add: poly_mapping_eq_iff ext)
qed

lemma plus_MP_oalist [code]: "MP_oalist xs + MP_oalist ys = MP_oalist (OAlist_map2_val_neutr_ntm (\<lambda>_. (+)) xs ys)"
  by (rule poly_mapping_eqI, simp add: lookup_plus_fun, rule oa_ntm.lookup_map2_val_neutr[symmetric], simp_all)

lemma minus_MP_oalist [code]: "MP_oalist xs - MP_oalist ys = MP_oalist (OAlist_map2_val_rneutr_ntm (\<lambda>_. (-)) xs ys)"
  by (rule poly_mapping_eqI, simp add: lookup_minus_fun, rule oa_ntm.lookup_map2_val_rneutr[symmetric], simp)

lemma uminus_MP_oalist [code]: "- MP_oalist xs = MP_oalist (OAlist_map_val_ntm (\<lambda>_. uminus) xs)"
  by (rule poly_mapping_eqI, simp, rule oa_ntm.lookup_map_val[symmetric], simp)

lemma equal_MP_oalist [code]: "equal_class.equal (MP_oalist xs) (MP_oalist ys) = (OAlist_eq_ntm xs ys)"
  by (simp add: oa_ntm.oalist_eq_alt equal_eq poly_mapping_eq_iff)

lemma map_MP_oalist [code]: "Poly_Mapping.map f (MP_oalist xs) = MP_oalist (OAlist_map_val_ntm (\<lambda>_. f) xs)"
proof -
  have eq: "OAlist_map_val_ntm (\<lambda>_. f) xs = OAlist_map_val_ntm (\<lambda>_ c. f c when c \<noteq> 0) xs"
  proof (rule oa_ntm.map_val_cong)
    fix t c
    assume *: "(t, c) \<in> set (fst (list_of_oalist_ntm xs))"
    hence "fst (t, c) \<in> fst ` set (fst (list_of_oalist_ntm xs))" by (rule imageI)
    hence "OAlist_lookup_ntm xs t \<noteq> 0"
      by (simp add: oa_ntm.in_sorted_domain_iff_lookup[simplified oa_ntm.set_sorted_domain])
    moreover from * have "OAlist_lookup_ntm xs t = c" by (rule oa_ntm.lookup_eq_valueI)
    ultimately have "c \<noteq> 0" by simp
    thus "f c = (f c when c \<noteq> 0)" by simp
  qed
  show ?thesis
    by (rule poly_mapping_eqI, simp add: Poly_Mapping.map.rep_eq eq, rule oa_ntm.lookup_map_val[symmetric], simp)
qed

lemma range_MP_oalist [code]: "Poly_Mapping.range (MP_oalist xs) = set (map snd (fst (list_of_oalist_ntm xs)))"
proof (simp add: Poly_Mapping.range.rep_eq, intro set_eqI iffI)
  fix c
  assume "c \<in> range (OAlist_lookup_ntm xs) - {0}"
  hence "c \<in> range (OAlist_lookup_ntm xs)" and "c \<noteq> 0" by simp_all
  from this(1) obtain t where "OAlist_lookup_ntm xs t = c" by fastforce
  with \<open>c \<noteq> 0\<close> have "(t, c) \<in> set (fst (list_of_oalist_ntm xs))" by (simp add: oa_ntm.lookup_eq_value)
  hence "snd (t, c) \<in> snd ` set (fst (list_of_oalist_ntm xs))" by (rule imageI)
  thus "c \<in> snd ` set (fst (list_of_oalist_ntm xs))" by simp
next
  fix c
  assume "c \<in> snd ` set (fst (list_of_oalist_ntm xs))"
  then obtain t where *: "(t, c) \<in> set (fst (list_of_oalist_ntm xs))" by fastforce
  hence "fst (t, c) \<in> fst ` set (fst (list_of_oalist_ntm xs))" by (rule imageI)
  hence "OAlist_lookup_ntm xs t \<noteq> 0"
    by (simp add: oa_ntm.in_sorted_domain_iff_lookup[simplified oa_ntm.set_sorted_domain])
  moreover from * have "OAlist_lookup_ntm xs t = c" by (rule oa_ntm.lookup_eq_valueI)
  ultimately show "c \<in> range (OAlist_lookup_ntm xs) - {0}" by fastforce
qed

lemma if_poly_mapping_eq_iff:
  "(if x = y then a else b) = (if (\<forall>i\<in>keys x \<union> keys y. lookup x i = lookup y i) then a else b)"
  by simp (metis UnI1 UnI2 in_keys_iff poly_mapping_eqI)

lemma keys_add_eq: "keys (a + b) = keys a \<union> keys b - {x \<in> keys a \<inter> keys b. lookup a x + lookup b x = 0}"
  by (auto simp: in_keys_iff lookup_add add_eq_0_iff
      simp del: lookup_not_eq_zero_eq_in_keys)

locale gd_nat_term =
    gd_term pair_of_term term_of_pair
        "\<lambda>s t. le_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"
        "\<lambda>s t. lt_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"
        "le_of_nat_term_order cmp_term"
        "lt_of_nat_term_order cmp_term"
      for pair_of_term::"'t::nat_term \<Rightarrow> ('a::{nat_term,graded_dickson_powerprod} \<times> 'k::{countable,the_min,wellorder})"
      and term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
      and cmp_term +
    assumes splus_eq_splus: "t \<oplus> u = nat_term_class.splus (term_of_pair (t, the_min)) u"
begin

definition shift_map_keys :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('t, 'b) oalist_ntm \<Rightarrow> ('t, 'b::semiring_0) oalist_ntm"
  where "shift_map_keys t f xs = OAlist_ntm (map_raw (\<lambda>kv. (t \<oplus> fst kv, f (snd kv))) (list_of_oalist_ntm xs))"

lemma list_of_oalist_shift_keys:
  "list_of_oalist_ntm (shift_map_keys t f xs) = (map_raw (\<lambda>kv. (t \<oplus> fst kv, f (snd kv))) (list_of_oalist_ntm xs))"
  unfolding shift_map_keys_def
  by (rule oa_ntm.list_of_oalist_of_list_id, rule ko_ntm.oalist_inv_map_raw, fact oalist_inv_list_of_oalist_ntm,
      simp add: nat_term_compare_inv_conv[symmetric] nat_term_compare_inv_def splus_eq_splus nat_term_compare_splus)

lemma lookup_shift_map_keys_plus:
  "lookup (MP_oalist (shift_map_keys t ((*) c) xs)) (t \<oplus> u) = c * lookup (MP_oalist xs) u" (is "?l = ?r")
proof -
  let ?f = "\<lambda>kv. (t \<oplus> fst kv, c * snd kv)"
  have "?l = lookup_ko_ntm (map_raw ?f (list_of_oalist_ntm xs)) (fst (?f (u, c)))"
    by (simp add: oa_ntm.lookup_def list_of_oalist_shift_keys)
  also have "... = snd (?f (u, lookup_ko_ntm (list_of_oalist_ntm xs) u))"
    by (rule ko_ntm.lookup_raw_map_raw, fact oalist_inv_list_of_oalist_ntm, simp,
        simp add: nat_term_compare_inv_conv[symmetric] nat_term_compare_inv_def splus_eq_splus nat_term_compare_splus)
  also have "... = ?r" by (simp add: oa_ntm.lookup_def)
  finally show ?thesis .
qed

lemma keys_shift_map_keys_subset:
  "keys (MP_oalist (shift_map_keys t ((*) c) xs)) \<subseteq> ((\<oplus>) t) ` keys (MP_oalist xs)" (is "?l \<subseteq> ?r")
proof -
  let ?f = "\<lambda>kv. (t \<oplus> fst kv, c * snd kv)"
  have "?l = fst ` set (fst (map_raw ?f (list_of_oalist_ntm xs)))"
    by (simp add: keys_MP_oalist list_of_oalist_shift_keys)
  also from ko_ntm.map_raw_subset have "... \<subseteq> fst ` ?f ` set (fst (list_of_oalist_ntm xs))"
    by (rule image_mono)
  also have "... \<subseteq> ?r" by (simp add: keys_MP_oalist image_image)
  finally show ?thesis .
qed

lemma monom_mult_MP_oalist [code]:
  "monom_mult c t (MP_oalist xs) =
    MP_oalist (if c = 0 then OAlist_empty_ntm (snd (list_of_oalist_ntm xs)) else shift_map_keys t ((*) c) xs)"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (MP_oalist xs) = 0" using monom_mult_zero_left by simp
  thus ?thesis using True by simp
next
  case False
  have "monom_mult c t (MP_oalist xs) = MP_oalist (shift_map_keys t ((*) c) xs)"
  proof (rule poly_mapping_eqI, simp add: lookup_monom_mult del: MP_oalist.rep_eq, intro conjI impI)
    fix u
    assume "t adds\<^sub>p u"
    then obtain v where "u = t \<oplus> v" by (rule adds_ppE)
    thus "c * lookup (MP_oalist xs) (u \<ominus> t) = lookup (MP_oalist (shift_map_keys t ((*) c) xs)) u"
      by (simp add: splus_sminus lookup_shift_map_keys_plus del: MP_oalist.rep_eq)
  next
    fix u
    assume "\<not> t adds\<^sub>p u"
    have "u \<notin> keys (MP_oalist (shift_map_keys t ((*) c) xs))"
    proof
      assume "u \<in> keys (MP_oalist (shift_map_keys t ((*) c) xs))"
      also have "... \<subseteq> ((\<oplus>) t) ` keys (MP_oalist xs)" by (fact keys_shift_map_keys_subset)
      finally obtain v where "u = t \<oplus> v" ..
      hence "t adds\<^sub>p u" by (rule adds_ppI)
      with \<open>\<not> t adds\<^sub>p u\<close> show False ..
    qed
    thus "lookup (MP_oalist (shift_map_keys t ((*) c) xs)) u = 0" by (simp add: in_keys_iff)
  qed
  thus ?thesis by (simp add: False)
qed

lemma mult_scalar_MP_oalist [code]:
  "(MP_oalist xs) \<odot> (MP_oalist ys) =
      (if is_zero (MP_oalist xs) then
        MP_oalist (OAlist_empty_ntm (snd (list_of_oalist_ntm ys)))
      else
        let ct = OAlist_hd_ntm xs in
        monom_mult (snd ct) (fst ct) (MP_oalist ys) + (MP_oalist (OAlist_tl_ntm xs)) \<odot> (MP_oalist ys))"
proof (split if_split, intro conjI impI)
  assume "is_zero (MP_oalist xs)"
  thus "MP_oalist xs \<odot> MP_oalist ys = MP_oalist (OAlist_empty_ntm (snd (list_of_oalist_ntm ys)))"
    by (simp add: is_zero_def)
next
  assume "\<not> is_zero (MP_oalist xs)"
  hence *: "fst (list_of_oalist_ntm xs) \<noteq> []" by (simp add: is_zero_MP_oalist List.null_def)
  define ct where "ct = OAlist_hd_ntm xs"
  have eq: "except (MP_oalist xs) {fst ct} = MP_oalist (OAlist_tl_ntm xs)"
    by (rule poly_mapping_eqI, simp add: lookup_except ct_def oa_ntm.lookup_tl')
  have "MP_oalist xs \<odot> MP_oalist ys =
          monom_mult (lookup (MP_oalist xs) (fst ct)) (fst ct) (MP_oalist ys) +
          except (MP_oalist xs) {fst ct} \<odot> MP_oalist ys" by (fact mult_scalar_rec_left)
  also have "... = monom_mult (snd ct) (fst ct) (MP_oalist ys) + except (MP_oalist xs) {fst ct} \<odot> MP_oalist ys"
    using * by (simp add: ct_def oa_ntm.snd_hd)
  also have "... = monom_mult (snd ct) (fst ct) (MP_oalist ys) + MP_oalist (OAlist_tl_ntm xs) \<odot> MP_oalist ys"
    by (simp only: eq)
  finally show "MP_oalist xs \<odot> MP_oalist ys =
                (let ct = OAlist_hd_ntm xs in
                  monom_mult (snd ct) (fst ct) (MP_oalist ys) + MP_oalist (OAlist_tl_ntm xs) \<odot> MP_oalist ys)"
    by (simp add: ct_def Let_def)
qed

end (* ordered_nat_term *)

subsubsection \<open>Special case of addition: adding monomials\<close>

definition plus_monomial_less :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::monoid_add)"
  where "plus_monomial_less p c u = p + monomial c u"

text \<open>@{const plus_monomial_less} is useful when adding a monomial to a polynomial, where the term
  of the monomial is known to be smaller than all terms in the polynomial, because it can be
  implemented more efficiently than general addition.\<close>

lemma plus_monomial_less_MP_oalist [code]:
  "plus_monomial_less (MP_oalist xs) c u = MP_oalist (OAlist_update_by_fun_gr_ntm u (\<lambda>c0. c0 + c) xs)"
  unfolding plus_monomial_less_def oa_ntm.update_by_fun_gr_eq_update_by_fun
  by (rule poly_mapping_eqI, simp add: lookup_plus_fun oa_ntm.lookup_update_by_fun lookup_single)

text \<open>@{const plus_monomial_less} is computed by @{const OAlist_update_by_fun_gr_ntm}, because greater
  terms come @{emph \<open>before\<close>} smaller ones in @{type oalist_ntm}.\<close>

subsubsection \<open>Constructors\<close>

definition "distr\<^sub>0 ko xs = MP_oalist (oalist_of_list_ntm (xs, ko))" \<comment>\<open>sparse representation\<close>

definition V\<^sub>0 :: "'a \<Rightarrow> ('a, nat) pp \<Rightarrow>\<^sub>0 'b::{one,zero}" where
  "V\<^sub>0 n \<equiv> monomial 1 (single_pp n 1)"

definition C\<^sub>0 :: "'b \<Rightarrow> ('a, nat) pp \<Rightarrow>\<^sub>0 'b::zero" where "C\<^sub>0 c \<equiv> monomial c 0"

lemma C\<^sub>0_one: "C\<^sub>0 1 = 1"
  by (simp add: C\<^sub>0_def)

lemma C\<^sub>0_numeral: "C\<^sub>0 (numeral x) = numeral x"
  by (auto intro!: poly_mapping_eqI simp: C\<^sub>0_def lookup_numeral)

lemma C\<^sub>0_minus: "C\<^sub>0 (- x) = - C\<^sub>0 x"
  by (simp add: C\<^sub>0_def single_uminus)

lemma C\<^sub>0_zero: "C\<^sub>0 0 = 0"
  by (auto intro!: poly_mapping_eqI simp: C\<^sub>0_def)

lemma V\<^sub>0_power: "V\<^sub>0 v ^ n = monomial 1 (single_pp v n)"
  by (induction n) (auto simp: V\<^sub>0_def mult_single single_pp_plus)

lemma single_MP_oalist [code]: "Poly_Mapping.single k v = distr\<^sub>0 nat_term_order_of_le [(k, v)]"
  unfolding distr\<^sub>0_def by (rule poly_mapping_eqI, simp add: lookup_single OAlist_lookup_ntm_single)

lemma one_MP_oalist [code]: "1 = distr\<^sub>0 nat_term_order_of_le [(0, 1)]"
  by (metis single_MP_oalist single_one)

lemma except_MP_oalist [code]: "except (MP_oalist xs) S = MP_oalist (OAlist_filter_ntm (\<lambda>kv. fst kv \<notin> S) xs)"
  by (rule poly_mapping_eqI, simp add: lookup_except oa_ntm.lookup_filter)

subsubsection \<open>Changing the Internal Order\<close>

definition change_ord :: "'a::nat_term_compare nat_term_order \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "change_ord to = (\<lambda>x. x)"

lemma change_ord_MP_oalist [code]: "change_ord to (MP_oalist xs) = MP_oalist (OAlist_reorder_ntm to xs)"
  by (rule poly_mapping_eqI, simp add: change_ord_def oa_ntm.lookup_reorder)

subsubsection \<open>Ordered Power-Products\<close>

lemma foldl_assoc:
  assumes "\<And>x y z. f (f x y) z = f x (f y z)"
  shows "foldl f (f a b) xs = f a (foldl f b xs)"
proof (induct xs arbitrary: a b)
  fix a b
  show "foldl f (f a b) [] = f a (foldl f b [])" by simp
next
  fix a b x xs
  assume "\<And>a b. foldl f (f a b) xs = f a (foldl f b xs)"
  from assms[of a b x] this[of a "f b x"]
    show "foldl f (f a b) (x # xs) = f a (foldl f b (x # xs))" unfolding foldl_Cons by simp
  qed

context gd_nat_term
begin

definition ord_pp :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "ord_pp s t = le_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"

definition ord_pp_strict :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "ord_pp_strict s t = lt_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"

lemma lt_MP_oalist [code]:
  "lt (MP_oalist xs) = (if is_zero (MP_oalist xs) then min_term else fst (OAlist_min_key_val_ntm cmp_term xs))"
proof (split if_split, intro conjI impI)
  assume "is_zero (MP_oalist xs)"
  thus "lt (MP_oalist xs) = min_term" by (simp add: is_zero_def)
next
  assume "\<not> is_zero (MP_oalist xs)"
  hence "fst (list_of_oalist_ntm xs) \<noteq> []" by (simp add: is_zero_MP_oalist List.null_def)
  show "lt (MP_oalist xs) = fst (OAlist_min_key_val_ntm cmp_term xs)"
  proof (rule lt_eqI_keys)
    show "fst (OAlist_min_key_val_ntm cmp_term xs) \<in> keys (MP_oalist xs)"
      by (simp add: keys_MP_oalist, rule imageI, rule oa_ntm.min_key_val_in, fact)
  next
    fix u
    assume "u \<in> keys (MP_oalist xs)"
    also have "... = fst ` set (fst (list_of_oalist_ntm xs))" by (simp add: keys_MP_oalist)
    finally obtain z where "z \<in> set (fst (list_of_oalist_ntm xs))" and "u = fst z" ..
    from this(1) have "ko.le (key_order_of_nat_term_order_inv cmp_term) (fst (OAlist_min_key_val_ntm cmp_term xs)) u"
      unfolding \<open>u = fst z\<close> by (rule oa_ntm.min_key_val_minimal)
    thus "le_of_nat_term_order cmp_term u (fst (OAlist_min_key_val_ntm cmp_term xs))"
      by (simp add: le_of_nat_term_order_alt)
  qed
qed

lemma lc_MP_oalist [code]:
  "lc (MP_oalist xs) = (if is_zero (MP_oalist xs) then 0 else snd (OAlist_min_key_val_ntm cmp_term xs))"
proof (split if_split, intro conjI impI)
  assume "is_zero (MP_oalist xs)"
  thus "lc (MP_oalist xs) = 0" by (simp add: is_zero_def)
next
  assume "\<not> is_zero (MP_oalist xs)"
  moreover from this have "fst (list_of_oalist_ntm xs) \<noteq> []" by (simp add: is_zero_MP_oalist List.null_def)
  ultimately show "lc (MP_oalist xs) = snd (OAlist_min_key_val_ntm cmp_term xs)"
    by (simp add: lc_def lt_MP_oalist oa_ntm.snd_min_key_val)
qed

lemma tail_MP_oalist [code]: "tail (MP_oalist xs) = MP_oalist (OAlist_except_min_ntm cmp_term xs)"
proof (cases "is_zero (MP_oalist xs)")
  case True
  hence "fst (list_of_oalist_ntm xs) = []" by (simp add: is_zero_MP_oalist List.null_def)
  hence "fst (list_of_oalist_ntm (OAlist_except_min_ntm cmp_term xs)) = []"
    by (rule oa_ntm.except_min_Nil)
  hence "is_zero (MP_oalist (OAlist_except_min_ntm cmp_term xs))"
    by (simp add: is_zero_MP_oalist List.null_def)
  with True show ?thesis by (simp add: is_zero_def)
next
  case False
  show ?thesis by (rule poly_mapping_eqI, simp add: lookup_tail_2 oa_ntm.lookup_except_min' lt_MP_oalist False)
qed

definition comp_opt_p :: "('t \<Rightarrow>\<^sub>0 'c::zero, 't \<Rightarrow>\<^sub>0 'c) comp_opt"
  where "comp_opt_p p q =
              (if p = q then Some Eq else if ord_strict_p p q then Some Lt else if ord_strict_p q p then Some Gt else None)"

lemma comp_opt_p_MP_oalist [code]:
  "comp_opt_p (MP_oalist xs) (MP_oalist ys) =
    OAlist_lex_ord_ntm cmp_term (\<lambda>_ x y. if x = y then Some Eq else if x = 0 then Some Lt else if y = 0 then Some Gt else None) xs ys"
proof -
  let ?f = "\<lambda>_ x y. if x = y then Some Eq else if x = 0 then Some Lt else if y = 0 then Some Gt else None"
  show ?thesis
  proof (cases "comp_opt_p (MP_oalist xs) (MP_oalist ys) = Some Eq")
    case True
    hence "MP_oalist xs = MP_oalist ys" by (simp add: comp_opt_p_def split: if_splits)
    hence "lookup (MP_oalist xs) = lookup (MP_oalist ys)" by (rule arg_cong)
    hence eq: "OAlist_lookup_ntm xs = OAlist_lookup_ntm ys" by simp
    have "OAlist_lex_ord_ntm cmp_term ?f xs ys = Some Eq"
      by (rule oa_ntm.lex_ord_EqI, simp add: eq)
    with True show ?thesis by simp
  next
    case False
    hence neq: "MP_oalist xs \<noteq> MP_oalist ys" by (simp add: comp_opt_p_def split: if_splits)
    then obtain v where 1: "v \<in> keys (MP_oalist xs) \<union> keys (MP_oalist ys)"
      and 2: "lookup (MP_oalist xs) v \<noteq> lookup (MP_oalist ys) v"
      and 3: "\<And>u. lt_of_nat_term_order cmp_term v u \<Longrightarrow> lookup (MP_oalist xs) u = lookup (MP_oalist ys) u"
      by (rule poly_mapping_neqE, blast)
    show ?thesis
    proof (rule HOL.sym, rule oa_ntm.lex_ord_valI)
      from 1 show "v \<in> fst ` set (fst (list_of_oalist_ntm xs)) \<union> fst ` set (fst (list_of_oalist_ntm ys))"
        by (simp add: keys_MP_oalist)
    next
      from 2 have 4: "OAlist_lookup_ntm xs v \<noteq> OAlist_lookup_ntm ys v" by simp
      show "comp_opt_p (MP_oalist xs) (MP_oalist ys) =
            (if OAlist_lookup_ntm xs v = OAlist_lookup_ntm ys v then Some Eq
             else if OAlist_lookup_ntm xs v = 0 then Some Lt
             else if OAlist_lookup_ntm ys v = 0 then Some Gt else None)"
      proof (simp add: 4, intro conjI impI)
        assume "OAlist_lookup_ntm ys v = 0" and "OAlist_lookup_ntm xs v = 0"
        with 4 show "comp_opt_p (MP_oalist xs) (MP_oalist ys) = Some Lt" by simp
      next
        assume "OAlist_lookup_ntm xs v \<noteq> 0" and "OAlist_lookup_ntm ys v = 0"
        hence "lookup (MP_oalist ys) v = 0" and "lookup (MP_oalist xs) v \<noteq> 0" by simp_all
        hence "ord_strict_p (MP_oalist ys) (MP_oalist xs)" using 3[symmetric]
          by (rule ord_strict_pI)
        with neq show "comp_opt_p (MP_oalist xs) (MP_oalist ys) = Some Gt" by (auto simp: comp_opt_p_def)
      next
        assume "OAlist_lookup_ntm ys v \<noteq> 0" and "OAlist_lookup_ntm xs v = 0"
        hence "lookup (MP_oalist xs) v = 0" and "lookup (MP_oalist ys) v \<noteq> 0" by simp_all
        hence "ord_strict_p (MP_oalist xs) (MP_oalist ys)" using 3 by (rule ord_strict_pI)
        with neq show "comp_opt_p (MP_oalist xs) (MP_oalist ys) = Some Lt" by (auto simp: comp_opt_p_def)
      next
        assume "OAlist_lookup_ntm xs v \<noteq> 0"
        hence "lookup (MP_oalist xs) v \<noteq> 0" by simp
        with 2 have a: "\<not> ord_strict_p (MP_oalist xs) (MP_oalist ys)" using 3 by (rule not_ord_strict_pI)
        assume "OAlist_lookup_ntm ys v \<noteq> 0"
        hence "lookup (MP_oalist ys) v \<noteq> 0" by simp
        with 2[symmetric] have "\<not> ord_strict_p (MP_oalist ys) (MP_oalist xs)"
          using 3[symmetric] by (rule not_ord_strict_pI)
        with neq a show "comp_opt_p (MP_oalist xs) (MP_oalist ys) = None" by (auto simp: comp_opt_p_def)
      qed
    next
      fix u
      assume "ko.lt (key_order_of_nat_term_order_inv cmp_term) u v"
      hence "lt_of_nat_term_order cmp_term v u" by (simp only: lt_of_nat_term_order_alt)
      hence "lookup (MP_oalist xs) u = lookup (MP_oalist ys) u" by (rule 3)
      thus "(if OAlist_lookup_ntm xs u = OAlist_lookup_ntm ys u then Some Eq
            else if OAlist_lookup_ntm xs u = 0 then Some Lt
            else if OAlist_lookup_ntm ys u = 0 then Some Gt else None) = Some Eq" by simp
    qed fact
  qed
qed

lemma compute_ord_p [code]: "ord_p p q = (let aux = comp_opt_p p q in aux = Some Lt \<or> aux = Some Eq)"
  by (auto simp: ord_p_def comp_opt_p_def)

lemma compute_ord_p_strict [code]: "ord_strict_p p q = (comp_opt_p p q = Some Lt)"
  by (auto simp: comp_opt_p_def)

lemma keys_to_list_MP_oalist [code]: "keys_to_list (MP_oalist xs) = OAlist_sorted_domain_ntm cmp_term xs"
proof -
  have eq: "ko.lt (key_order_of_nat_term_order_inv cmp_term) = ord_term_strict_conv"
    by (intro ext, simp add: lt_of_nat_term_order_alt)
  have 1: "irreflp ord_term_strict_conv" by (rule irreflpI, simp)
  have 2: "transp ord_term_strict_conv" by (rule transpI, simp)
  have "antisymp ord_term_strict_conv" by (rule antisympI, simp)
  moreover have 3: "sorted_wrt ord_term_strict_conv (keys_to_list (MP_oalist xs))"
    unfolding keys_to_list_def by (fact pps_to_list_sorted_wrt)
  moreover note _
  moreover have 4: "sorted_wrt ord_term_strict_conv (OAlist_sorted_domain_ntm cmp_term xs)"
    unfolding eq[symmetric] by (fact oa_ntm.sorted_sorted_domain)
  ultimately show ?thesis
  proof (rule sorted_wrt_distinct_set_unique)
    from 1 2 3 show "distinct (keys_to_list (MP_oalist xs))" by (rule distinct_sorted_wrt_irrefl)
  next
    from 1 2 4 show "distinct (OAlist_sorted_domain_ntm cmp_term xs)" by (rule distinct_sorted_wrt_irrefl)
  next
    show "set (keys_to_list (MP_oalist xs)) = set (OAlist_sorted_domain_ntm cmp_term xs)"
      by (simp add: set_keys_to_list keys_MP_oalist oa_ntm.set_sorted_domain)
  qed
qed

end (* ordered_nat_term *)

lifting_update poly_mapping.lifting
lifting_forget poly_mapping.lifting

subsection \<open>Interpretations\<close>

lemma term_powerprod_gd_term:
  fixes pair_of_term :: "'t::nat_term \<Rightarrow> ('a::{graded_dickson_powerprod,nat_pp_compare} \<times> 'k::{the_min,wellorder})"
  assumes "term_powerprod pair_of_term term_of_pair"
    and "\<And>v. fst (rep_nat_term v) = rep_nat_pp (fst (pair_of_term v))"
    and "\<And>t. snd (rep_nat_term (term_of_pair (t, the_min))) = 0"
    and "\<And>v w. snd (pair_of_term v) \<le> snd (pair_of_term w) \<Longrightarrow> snd (rep_nat_term v) \<le> snd (rep_nat_term w)"
    and "\<And>s t k. term_of_pair (s + t, k) = splus (term_of_pair (s, k)) (term_of_pair (t, k))"
    and "\<And>t v. term_powerprod.splus pair_of_term term_of_pair t v = splus (term_of_pair (t, the_min)) v"
  shows "gd_term pair_of_term term_of_pair
        (\<lambda>s t. le_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min)))
        (\<lambda>s t. lt_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min)))
        (le_of_nat_term_order cmp_term)
        (lt_of_nat_term_order cmp_term)"
proof -
  from assms(1) interpret tp: term_powerprod pair_of_term term_of_pair .
  let ?f = "\<lambda>x. term_of_pair (x, the_min)"
  show ?thesis
  proof (intro gd_term.intro ordered_term.intro)
    from assms(1) show "term_powerprod pair_of_term term_of_pair" .
  next
    show "ordered_powerprod (\<lambda>s t. le_of_nat_term_order cmp_term (?f s) (?f t))
                        (\<lambda>s t. lt_of_nat_term_order cmp_term (?f s) (?f t))"
    proof (intro ordered_powerprod.intro ordered_powerprod_axioms.intro)
      show "class.linorder (\<lambda>s t. le_of_nat_term_order cmp_term (?f s) (?f t))
                        (\<lambda>s t. lt_of_nat_term_order cmp_term (?f s) (?f t))"
      proof (unfold_locales, simp_all add: lt_of_nat_term_order_alt le_of_nat_term_order_alt ko.linear ko.less_le_not_le)
        fix x y
        assume "ko.le (key_order_of_nat_term_order_inv cmp_term) (term_of_pair (x, the_min)) (term_of_pair (y, the_min))"
          and "ko.le (key_order_of_nat_term_order_inv cmp_term) (term_of_pair (y, the_min)) (term_of_pair (x, the_min))"
        hence "term_of_pair (x, the_min) = term_of_pair (y, the_min)" by (rule ko.antisym)
        hence "(x, the_min) = (y, the_min::'k)" by (rule tp.term_of_pair_injective)
        thus "x = y" by simp
      qed
    next
      fix t
      show "le_of_nat_term_order cmp_term (?f 0) (?f t)"
        unfolding le_of_nat_term_order
        by (rule nat_term_compD1', fact comparator_nat_term_compare, fact nat_term_comp_nat_term_compare,
            simp add: assms(3), simp add: assms(2) zero_pp tp.pair_term)
    next
      fix s t u
      assume "le_of_nat_term_order cmp_term (?f s) (?f t)"
      hence "le_of_nat_term_order cmp_term (?f (u + s)) (?f (u + t))"
        by (simp add: le_of_nat_term_order assms(5) nat_term_compare_splus)
      thus "le_of_nat_term_order cmp_term (?f (s + u)) (?f (t + u))" by (simp only: ac_simps)
    qed
  next
    show "class.linorder (le_of_nat_term_order cmp_term) (lt_of_nat_term_order cmp_term)"
      by (fact linorder_le_of_nat_term_order)
  next
    show "ordered_term_axioms pair_of_term term_of_pair (\<lambda>s t. le_of_nat_term_order cmp_term (?f s) (?f t))
       (le_of_nat_term_order cmp_term)"
    proof
      fix v w t
      assume "le_of_nat_term_order cmp_term v w"
      thus "le_of_nat_term_order cmp_term (t \<oplus> v) (t \<oplus> w)"
        by (simp add: le_of_nat_term_order assms(6) nat_term_compare_splus)
    next
      fix v w
      assume "le_of_nat_term_order cmp_term (?f (tp.pp_of_term v)) (?f (tp.pp_of_term w))"
      hence 3: "nat_term_compare cmp_term (?f (tp.pp_of_term v)) (?f (tp.pp_of_term w)) \<noteq> Gt"
        by (simp add: le_of_nat_term_order)
      assume "tp.component_of_term v \<le> tp.component_of_term w"
      hence 4: "snd (rep_nat_term v) \<le> snd (rep_nat_term w)"
        by (simp add: tp.component_of_term_def assms(4))
      note comparator_nat_term_compare nat_term_comp_nat_term_compare
      moreover have "fst (rep_nat_term v) = fst (rep_nat_term (?f (tp.pp_of_term v)))"
        by (simp add: assms(2) tp.pp_of_term_def tp.pair_term)
      moreover have "fst (rep_nat_term w) = fst (rep_nat_term (?f (tp.pp_of_term w)))"
        by (simp add: assms(2) tp.pp_of_term_def tp.pair_term)
      moreover note 4
      moreover have "snd (rep_nat_term (?f (tp.pp_of_term v))) = snd (rep_nat_term (?f (tp.pp_of_term w)))"
        by (simp add: assms(3))
      ultimately show "le_of_nat_term_order cmp_term v w" unfolding le_of_nat_term_order using 3
        by (rule nat_term_compD4'')
    qed
  qed
qed

lemma gd_term_to_pair_unit:
  "gd_term (to_pair_unit::'a::{nat_term_compare,nat_pp_term,graded_dickson_powerprod} \<Rightarrow> _) fst
        (\<lambda>s t. le_of_nat_term_order cmp_term (fst (s, the_min)) (fst (t, the_min)))
        (\<lambda>s t. lt_of_nat_term_order cmp_term (fst (s, the_min)) (fst (t, the_min)))
        (le_of_nat_term_order cmp_term)
        (lt_of_nat_term_order cmp_term)"
proof (intro gd_term.intro ordered_term.intro)
  show "term_powerprod to_pair_unit fst" by unfold_locales
next
  show "ordered_powerprod (\<lambda>s t. le_of_nat_term_order cmp_term (fst (s, the_min)) (fst (t, the_min)))
                      (\<lambda>s t. lt_of_nat_term_order cmp_term (fst (s, the_min)) (fst (t, the_min)))"
    unfolding fst_conv using linorder_le_of_nat_term_order
  proof (intro ordered_powerprod.intro)
    from le_of_nat_term_order_zero_min show "ordered_powerprod_axioms (le_of_nat_term_order cmp_term)"
    proof (unfold_locales)
      fix s t u
      assume "le_of_nat_term_order cmp_term s t"
      hence "le_of_nat_term_order cmp_term (u + s) (u + t)" by (rule le_of_nat_term_order_plus_monotone)
      thus "le_of_nat_term_order cmp_term (s + u) (t + u)" by (simp only: ac_simps)
    qed
  qed
next
  show "class.linorder (le_of_nat_term_order cmp_term) (lt_of_nat_term_order cmp_term)"
    by (fact linorder_le_of_nat_term_order)
next
  show "ordered_term_axioms to_pair_unit fst (\<lambda>s t. le_of_nat_term_order cmp_term (fst (s, the_min)) (fst (t, the_min)))
     (le_of_nat_term_order cmp_term)" by (unfold_locales, auto intro: le_of_nat_term_order_plus_monotone)
qed

corollary gd_nat_term_to_pair_unit:
  "gd_nat_term (to_pair_unit::'a::{nat_term_compare,nat_pp_term,graded_dickson_powerprod} \<Rightarrow> _) fst cmp_term"
  by (rule gd_nat_term.intro, fact gd_term_to_pair_unit, rule gd_nat_term_axioms.intro, simp add: splus_pp_term)

lemma gd_term_id:
  "gd_term (\<lambda>x::('a::{nat_term_compare,nat_pp_compare,nat_pp_term,graded_dickson_powerprod} \<times> 'b::{nat,the_min}). x) (\<lambda>x. x)
        (\<lambda>s t. le_of_nat_term_order cmp_term (s, the_min) (t, the_min))
        (\<lambda>s t. lt_of_nat_term_order cmp_term (s, the_min) (t, the_min))
        (le_of_nat_term_order cmp_term)
        (lt_of_nat_term_order cmp_term)"
  apply (rule term_powerprod_gd_term)
  subgoal by unfold_locales
  subgoal by (simp add: rep_nat_term_prod_def)
  subgoal by (simp add: rep_nat_term_prod_def the_min_eq_zero)
  subgoal by (simp add: rep_nat_term_prod_def ord_iff[symmetric])
  subgoal by (simp add: splus_prod_def pprod.splus_def)
  subgoal by (simp add: splus_prod_def)
  done

corollary gd_nat_term_id: "gd_nat_term (\<lambda>x. x) (\<lambda>x. x) cmp_term"
  for cmp_term :: "('a::{nat_term_compare,nat_pp_compare,nat_pp_term,graded_dickson_powerprod} \<times> 'c::{nat,the_min}) nat_term_order"
  by (rule gd_nat_term.intro, fact gd_term_id, rule gd_nat_term_axioms.intro, simp add: splus_prod_def)

subsection \<open>Computations\<close>

type_synonym 'a mpoly_tc = "(nat, nat) pp \<Rightarrow>\<^sub>0 'a"

global_interpretation punit0: gd_nat_term "to_pair_unit::'a::{nat_term_compare,nat_pp_term,graded_dickson_powerprod} \<Rightarrow> _" fst cmp_term
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  for cmp_term
  defines monom_mult_punit = punit.monom_mult
  and mult_scalar_punit = punit.mult_scalar
  and shift_map_keys_punit = punit0.shift_map_keys
  and ord_pp_punit = punit0.ord_pp
  and ord_pp_strict_punit = punit0.ord_pp_strict
  and min_term_punit = punit0.min_term
  and lt_punit = punit0.lt
  and lc_punit = punit0.lc
  and tail_punit = punit0.tail
  and comp_opt_p_punit = punit0.comp_opt_p
  and ord_p_punit = punit0.ord_p
  and ord_strict_p_punit = punit0.ord_strict_p
  and keys_to_list_punit = punit0.keys_to_list
  subgoal by (fact gd_nat_term_to_pair_unit)
  subgoal by (fact punit_adds_term)
  subgoal by (fact punit_pp_of_term)
  subgoal by (fact punit_component_of_term)
  done

lemma shift_map_keys_punit_MP_oalist [code abstract]:
  "list_of_oalist_ntm (shift_map_keys_punit t f xs) = map_raw (\<lambda>(k, v). (t + k, f v)) (list_of_oalist_ntm xs)"
  by (simp add: punit0.list_of_oalist_shift_keys case_prod_beta')

lemmas [code] = punit0.mult_scalar_MP_oalist[unfolded mult_scalar_punit_def punit_mult_scalar]
                punit0.punit_min_term

lemma ord_pp_punit_alt [code_unfold]: "ord_pp_punit = le_of_nat_term_order"
  by (intro ext, simp add: punit0.ord_pp_def)

lemma ord_pp_strict_punit_alt [code_unfold]: "ord_pp_strict_punit = lt_of_nat_term_order"
  by (intro ext, simp add: punit0.ord_pp_strict_def)

lemma gd_powerprod_ord_pp_punit: "gd_powerprod (ord_pp_punit cmp_term) (ord_pp_strict_punit cmp_term)"
  unfolding punit0.ord_pp_def punit0.ord_pp_strict_def ..

locale trivariate\<^sub>0_rat
begin

abbreviation X::"rat mpoly_tc" where "X \<equiv> V\<^sub>0 (0::nat)"
abbreviation Y::"rat mpoly_tc" where "Y \<equiv> V\<^sub>0 (1::nat)"
abbreviation Z::"rat mpoly_tc" where "Z \<equiv> V\<^sub>0 (2::nat)"

end

experiment begin interpretation trivariate\<^sub>0_rat .

value [code] "X ^ 2"

value [code] "X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2"

value [code] "distr\<^sub>0 DRLEX [(sparse\<^sub>0 [(0::nat, 3::nat)], 1::rat)] = distr\<^sub>0 DRLEX [(sparse\<^sub>0 [(0, 3)], 1)]"

lemma
  "ord_strict_p_punit DRLEX (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z\<^sup>2 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "tail_punit DLEX (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) = X\<^sup>2 * Z"
  by eval

value [code] "min_term_punit::(nat, nat) pp"

value [code] "is_zero (distr\<^sub>0 DRLEX [(sparse\<^sub>0 [(0::nat, 3::nat)], 1::rat)])"

value [code] "lt_punit DRLEX (distr\<^sub>0 DRLEX [(sparse\<^sub>0 [(0::nat, 3::nat)], 1::rat)])"

lemma
  "lt_punit DRLEX (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) = sparse\<^sub>0 [(1, 3), (2, 2)]"
  by eval

lemma
  "lt_punit DRLEX (X + Y + Z) = sparse\<^sub>0 [(2, 1)]"
  by eval

lemma
  "keys (X\<^sup>2 * Z ^ 3 + 2 * Y ^ 3 * Z\<^sup>2) =
    {sparse\<^sub>0 [(0, 2), (2, 3)], sparse\<^sub>0 [(1, 3), (2, 2)]}"
  by eval

lemma
  "- 1 * X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2 = - X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 = X\<^sup>2 * Z ^ 7 + X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 - X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 =
    X\<^sup>2 * Z ^ 7 - X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "lookup (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + 2) (sparse\<^sub>0 [(0, 2), (2, 7)]) = 1"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 \<noteq>
   X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval

lemma
  "0 * X^2 * Z^7 + 0 * Y^3*Z\<^sup>2 = 0"
  by eval

lemma
  "monom_mult_punit 3 (sparse\<^sub>0 [(1, 2::nat)]) (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) =
    3 * Y\<^sup>2 * Z * X\<^sup>2 + 6 * Y ^ 5 * Z\<^sup>2"
  by eval

lemma
  "monomial (-4) (sparse\<^sub>0 [(0, 2::nat)]) = - 4 * X\<^sup>2"
  by eval

lemma "monomial (0::rat) (sparse\<^sub>0 [(0::nat, 2::nat)]) = 0"
  by eval

lemma
  "(X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) * (X\<^sup>2 * Z ^ 3 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X ^ 4 * Z ^ 4 + - 2 * X\<^sup>2 * Z ^ 3 * Y ^ 3 +
 - 4 * Y ^ 6 * Z ^ 4 + 2 * Y ^ 3 * Z ^ 5 * X\<^sup>2"
  by eval

end

subsection \<open>Code setup for type MPoly\<close>

text \<open>postprocessing from \<open>Var\<^sub>0, Const\<^sub>0\<close> to \<open>Var, Const\<close>.\<close>

lemmas [code_post] =
  plus_mpoly.abs_eq[symmetric]
  times_mpoly.abs_eq[symmetric]
  one_mpoly_def[symmetric]
  Var.abs_eq[symmetric]
  Const.abs_eq[symmetric]

instantiation mpoly::("{equal, zero}")equal begin

lift_definition equal_mpoly:: "'a mpoly \<Rightarrow> 'a mpoly \<Rightarrow> bool" is HOL.equal .

instance proof standard qed (transfer, rule equal_eq)

end

end (* theory *)
