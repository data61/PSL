(* Author: Alexander Maletzky *)

section \<open>Sample Computations of Syzygies\<close>

theory Syzygy_Examples
  imports Buchberger Algorithm_Schema_Impl Syzygy Code_Target_Rat
begin

subsection \<open>Preparations\<close>

text \<open>We must define the following four constants outside the global interpretation, since otherwise
  their types are too general.\<close>

definition splus_pprod :: "('a::nat, 'b::nat) pp \<Rightarrow> _"
  where "splus_pprod = pprod.splus"

definition monom_mult_pprod :: "'c::semiring_0 \<Rightarrow> ('a::nat, 'b::nat) pp \<Rightarrow> ((('a, 'b) pp \<times> nat) \<Rightarrow>\<^sub>0 'c) \<Rightarrow> _"
  where "monom_mult_pprod = pprod.monom_mult"

definition mult_scalar_pprod :: "(('a::nat, 'b::nat) pp \<Rightarrow>\<^sub>0 'c::semiring_0) \<Rightarrow> ((('a, 'b) pp \<times> nat) \<Rightarrow>\<^sub>0 'c) \<Rightarrow> _"
  where "mult_scalar_pprod = pprod.mult_scalar"

definition adds_term_pprod :: "(('a::nat, 'b::nat) pp \<times> _) \<Rightarrow> _"
  where "adds_term_pprod = pprod.adds_term"

lemma (in gd_term) compute_trd_aux [code]:
  "trd_aux fs p r =
    (if is_zero p then
      r
    else
      case find_adds fs (lt p) of
        None   \<Rightarrow> trd_aux fs (tail p) (plus_monomial_less r (lc p) (lt p))
      | Some f \<Rightarrow> trd_aux fs (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) r
    )"
  by (simp only: trd_aux.simps[of fs p r] plus_monomial_less_def is_zero_def)

locale gd_nat_inf_term = gd_nat_term pair_of_term term_of_pair cmp_term
    for pair_of_term::"'t::nat_term \<Rightarrow> ('a::{nat_term,graded_dickson_powerprod} \<times> nat)"
    and term_of_pair::"('a \<times> nat) \<Rightarrow> 't"
    and cmp_term
begin

sublocale aux: gd_inf_term pair_of_term term_of_pair
        "\<lambda>s t. le_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"
        "\<lambda>s t. lt_of_nat_term_order cmp_term (term_of_pair (s, the_min)) (term_of_pair (t, the_min))"
        "le_of_nat_term_order cmp_term"
        "lt_of_nat_term_order cmp_term" ..

definition lift_keys :: "nat \<Rightarrow> ('t, 'b) oalist_ntm \<Rightarrow> ('t, 'b::semiring_0) oalist_ntm"
  where "lift_keys i xs = oalist_of_list_ntm (map_raw (\<lambda>kv. (map_component ((+) i) (fst kv), snd kv)) (list_of_oalist_ntm xs))"

lemma list_of_oalist_lift_keys:
  "list_of_oalist_ntm (lift_keys i xs) = (map_raw (\<lambda>kv. (map_component ((+) i) (fst kv), snd kv)) (list_of_oalist_ntm xs))"
  unfolding lift_keys_def oops

text \<open>Regardless of whether the above lemma holds (which might be the case) or not, we can use
  @{const lift_keys} in computations. Now, however, it is implemented rather inefficiently, because
  the list resulting from the application of @{const map_raw} is sorted again. That should not be
  a big problem though, since @{const lift_keys} is applied only once to every input polynomial
  before computing syzygies.\<close>

lemma lookup_lift_keys_plus:
  "lookup (MP_oalist (lift_keys i xs)) (term_of_pair (t, i + k)) = lookup (MP_oalist xs) (term_of_pair (t, k))"
    (is "?l = ?r")
proof -
  let ?f = "\<lambda>kv::'t \<times> 'b. (map_component ((+) i) (fst kv), snd kv)"
  obtain xs' ox where xs: "list_of_oalist_ntm xs = (xs', ox)" by fastforce
  from oalist_inv_list_of_oalist_ntm[of xs] have inv: "ko_ntm.oalist_inv_raw ox xs'"
    by (simp add: xs ko_ntm.oalist_inv_def nat_term_compare_inv_conv)
  let ?rel = "ko.lt (key_order_of_nat_term_order_inv ox)"
  have "irreflp ?rel" by (simp add: irreflp_def)
  moreover have "transp ?rel" by (simp add: lt_of_nat_term_order_alt)
  moreover from oa_ntm.list_of_oalist_sorted[of xs]
  have "sorted_wrt (ko.lt (key_order_of_nat_term_order_inv ox)) (map fst xs')" by (simp add: xs)
  ultimately have dist1: "distinct (map fst xs')" by (rule distinct_sorted_wrt_irrefl)
  have 1: "u = v" if "map_component ((+) i) u = map_component ((+) i) v" for u v
  proof -
    have "inj ((+) i)" by (simp add: inj_def)
    thus ?thesis using that by (rule map_component_inj)
  qed
  have dist2: "distinct (map fst (map_pair (\<lambda>kv. (map_component ((+) i) (fst kv), snd kv)) xs'))"
    by (rule ko_ntm.distinct_map_pair, fact dist1, simp add: 1)
  have "?l = lookup_dflt (map_pair ?f xs') (term_of_pair (t, i + k))"
    by (simp add: oa_ntm.lookup_def lift_keys_def xs oalist_of_list_ntm_def list_of_oalist_OAlist_ntm
        ko_ntm.lookup_pair_sort_oalist'[OF dist2])
  also have "... = lookup_dflt (map_pair ?f xs') (fst (?f (term_of_pair (t, k), b)))"
    by (simp add: map_component_term_of_pair)
  also have "... = snd (?f (term_of_pair (t, k), lookup_dflt xs' (term_of_pair (t, k))))"
    by (rule ko_ntm.lookup_dflt_map_pair, fact dist1, auto intro: 1)
  also have "... = ?r" by (simp add: oa_ntm.lookup_def xs ko_ntm.lookup_dflt_eq_lookup_pair[OF inv])
  finally show ?thesis .
qed

lemma keys_lift_keys_subset:
  "keys (MP_oalist (lift_keys i xs)) \<subseteq> (map_component ((+) i)) ` keys (MP_oalist xs)" (is "?l \<subseteq> ?r")
proof -
  let ?f = "\<lambda>kv::'t \<times> 'b. (map_component ((+) i) (fst kv), snd kv)"
  obtain xs' ox where xs: "list_of_oalist_ntm xs = (xs', ox)" by fastforce
  let ?rel = "ko.lt (key_order_of_nat_term_order_inv ox)"
  have "irreflp ?rel" by (simp add: irreflp_def)
  moreover have "transp ?rel" by (simp add: lt_of_nat_term_order_alt)
  moreover from oa_ntm.list_of_oalist_sorted[of xs]
  have "sorted_wrt (ko.lt (key_order_of_nat_term_order_inv ox)) (map fst xs')" by (simp add: xs)
  ultimately have dist1: "distinct (map fst xs')" by (rule distinct_sorted_wrt_irrefl)
  have 1: "u = v" if "map_component ((+) i) u = map_component ((+) i) v" for u v
  proof -
    have "inj ((+) i)" by (simp add: inj_def)
    thus ?thesis using that by (rule map_component_inj)
  qed
  have dist2: "distinct (map fst (map_pair (\<lambda>kv. (map_component ((+) i) (fst kv), snd kv)) xs'))"
    by (rule ko_ntm.distinct_map_pair, fact dist1, simp add: 1)
  have "?l \<subseteq> fst ` set (fst (map_raw ?f (list_of_oalist_ntm xs)))"
    by (auto simp: keys_MP_oalist lift_keys_def oalist_of_list_ntm_def list_of_oalist_OAlist_ntm xs
        ko_ntm.set_sort_oalist[OF dist2])
  also from ko_ntm.map_raw_subset have "... \<subseteq> fst ` ?f ` set (fst (list_of_oalist_ntm xs))"
    by (rule image_mono)
  also have "... \<subseteq> ?r" by (simp add: keys_MP_oalist image_image)
  finally show ?thesis .
qed

end

global_interpretation pprod': gd_nat_inf_term "\<lambda>x::('a, 'b) pp \<times> nat. x" "\<lambda>x. x" cmp_term
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.splus = splus_pprod"
  and "pprod.monom_mult = monom_mult_pprod"
  and "pprod.mult_scalar = mult_scalar_pprod"
  and "pprod.adds_term = adds_term_pprod"
  for cmp_term :: "(('a::nat, 'b::nat) pp \<times> nat) nat_term_order"
  defines shift_map_keys_pprod = pprod'.shift_map_keys
  and lift_keys_pprod = pprod'.lift_keys
  and min_term_pprod = pprod'.min_term
  and lt_pprod = pprod'.lt
  and lc_pprod = pprod'.lc
  and tail_pprod = pprod'.tail
  and comp_opt_p_pprod = pprod'.comp_opt_p
  and ord_p_pprod = pprod'.ord_p
  and ord_strict_p_pprod = pprod'.ord_strict_p
  and find_adds_pprod = pprod'.find_adds
  and trd_aux_pprod= pprod'.trd_aux
  and trd_pprod = pprod'.trd
  and spoly_pprod = pprod'.spoly
  and count_const_lt_components_pprod = pprod'.count_const_lt_components
  and count_rem_components_pprod = pprod'.count_rem_components
  and const_lt_component_pprod = pprod'.const_lt_component
  and full_gb_pprod = pprod'.full_gb
  and keys_to_list_pprod = pprod'.keys_to_list
  and Keys_to_list_pprod = pprod'.Keys_to_list
  and add_pairs_single_sorted_pprod = pprod'.add_pairs_single_sorted
  and add_pairs_pprod = pprod'.add_pairs
  and canon_pair_order_aux_pprod = pprod'.canon_pair_order_aux
  and canon_basis_order_pprod = pprod'.canon_basis_order
  and new_pairs_sorted_pprod = pprod'.new_pairs_sorted
  and component_crit_pprod = pprod'.component_crit
  and chain_ncrit_pprod = pprod'.chain_ncrit
  and chain_ocrit_pprod = pprod'.chain_ocrit
  and apply_icrit_pprod = pprod'.apply_icrit
  and apply_ncrit_pprod = pprod'.apply_ncrit
  and apply_ocrit_pprod = pprod'.apply_ocrit
  and trdsp_pprod = pprod'.trdsp
  and gb_sel_pprod = pprod'.gb_sel
  and gb_red_aux_pprod = pprod'.gb_red_aux
  and gb_red_pprod = pprod'.gb_red
  and gb_aux_pprod = pprod'.gb_aux
  and gb_pprod = pprod'.gb
  and filter_syzygy_basis_pprod = pprod'.aux.filter_syzygy_basis
  and init_syzygy_list_pprod = pprod'.aux.init_syzygy_list
  and lift_poly_syz_pprod = pprod'.aux.lift_poly_syz
  and map_component_pprod = pprod'.map_component
  subgoal by (rule gd_nat_inf_term.intro, fact gd_nat_term_id)
  subgoal by (fact pprod_pp_of_term)
  subgoal by (fact pprod_component_of_term)
  subgoal by (simp only: splus_pprod_def)
  subgoal by (simp only: monom_mult_pprod_def)
  subgoal by (simp only: mult_scalar_pprod_def)
  subgoal by (simp only: adds_term_pprod_def)
  done

lemma compute_adds_term_pprod [code]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pp_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pp_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_shift_map_keys_pprod [code abstract]:
  "list_of_oalist_ntm (shift_map_keys_pprod t f xs) = map_raw (\<lambda>(k, v). (splus_pprod t k, f v)) (list_of_oalist_ntm xs)"
  by (simp add: pprod'.list_of_oalist_shift_keys case_prod_beta')

lemma compute_trd_pprod [code]: "trd_pprod to fs p = trd_aux_pprod to fs p (change_ord to 0)"
  by (simp only: pprod'.trd_def change_ord_def)

lemmas [code] = conversep_iff

lemma POT_is_pot_ord: "pprod'.is_pot_ord (TYPE('a::nat)) (TYPE('b::nat)) (POT to)"
  by (rule pprod'.is_pot_ordI, simp add: lt_of_nat_term_order nat_term_compare_POT pot_comp rep_nat_term_prod_def,
      simp add: comparator_of_def)

definition Vec\<^sub>0 :: "nat \<Rightarrow> (('a, nat) pp \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a::nat, nat) pp \<times> nat) \<Rightarrow>\<^sub>0 'b::semiring_1" where
  "Vec\<^sub>0 i p = mult_scalar_pprod p (Poly_Mapping.single (0, i) 1)"

definition "syzygy_basis to bs =
    filter_syzygy_basis_pprod (length bs) (map fst (gb_pprod (POT to) (map (\<lambda>p. (p, ())) (init_syzygy_list_pprod bs)) ()))"

thm pprod'.aux.filter_syzygy_basis_isGB[OF POT_is_pot_ord]

lemma lift_poly_syz_MP_oalist [code]:
  "lift_poly_syz_pprod n (MP_oalist xs) i = MP_oalist (OAlist_insert_ntm ((0, i), 1) (lift_keys_pprod n xs))"
proof (rule poly_mapping_eqI, simp add: pprod'.aux.lookup_lift_poly_syz del: MP_oalist.rep_eq, intro conjI impI)
  fix v::"('a, 'b) pp \<times> nat"
  assume "n \<le> snd v"
  moreover obtain t k where "v = (t, k)" by fastforce
  ultimately have k: "n + (k - n) = k" by simp
  hence v: "v = (t, n + (k - n))" by (simp only: \<open>v = (t, k)\<close>)
  assume "v \<noteq> (0, i)"
  hence "lookup (MP_oalist (OAlist_insert_ntm ((0, i), 1) (lift_keys_pprod n xs))) v =
          lookup (MP_oalist (lift_keys_pprod n xs)) v" by (simp add: oa_ntm.lookup_insert)
  also have "... = lookup (MP_oalist xs) (t, k - n)" by (simp only: v pprod'.lookup_lift_keys_plus)
  also have "... = lookup (MP_oalist xs) (map_component_pprod (\<lambda>k. k - n) v)"
    by (simp add: v pprod'.map_component_term_of_pair)
  finally show "lookup (MP_oalist xs) (map_component_pprod (\<lambda>k. k - n) v) =
                  lookup (MP_oalist (OAlist_insert_ntm ((0, i), 1) (lift_keys_pprod n xs))) v" by (rule HOL.sym)
next
  fix v::"('a, 'b) pp \<times> nat"
  assume "\<not> n \<le> snd v"
  assume "v \<noteq> (0, i)"
  hence "lookup (MP_oalist (OAlist_insert_ntm ((0, i), 1) (lift_keys_pprod n xs))) v =
          lookup (MP_oalist (lift_keys_pprod n xs)) v" by (simp add: add: oa_ntm.lookup_insert)
  also have "... = 0"
  proof (rule ccontr)
    assume "lookup (MP_oalist (lift_keys_pprod n xs)) v \<noteq> 0"
    hence "v \<in> keys (MP_oalist (lift_keys_pprod n xs))" by (simp add: in_keys_iff del: MP_oalist.rep_eq)
    also have "... \<subseteq> map_component_pprod ((+) n) ` keys (MP_oalist xs)"
      by (fact pprod'.keys_lift_keys_subset)
    finally obtain u where "v = map_component_pprod ((+) n) u" ..
    hence "snd v = n + snd u" by (simp add: pprod'.component_of_map_component)
    with \<open>\<not> n \<le> snd v\<close> show False by simp
  qed
  finally show "lookup (MP_oalist (OAlist_insert_ntm ((0, i), 1) (lift_keys_pprod n xs))) v = 0" .
qed (simp_all add: oa_ntm.lookup_insert)

subsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "syzygy_basis DRLEX [Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (X * Y * Z + 2 * Y\<^sup>2)] =
  [Vec\<^sub>0 0 (C\<^sub>0 (1 / 3) * X * Y * Z + C\<^sub>0 (2 / 3) * Y\<^sup>2) + Vec\<^sub>0 1 (C\<^sub>0 (- 1 / 3) * X\<^sup>2 * Z ^ 3 - X\<^sup>2 * Y)]"
  by eval

value [code] "syzygy_basis DRLEX [Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (X * Y * Z + 2 * Y\<^sup>2), Vec\<^sub>0 0 (X - Y + 3 * Z)]"

lemma
  "map fst (gb_pprod (POT DRLEX) (map (\<lambda>p. (p, ())) (init_syzygy_list_pprod
    [Vec\<^sub>0 0 (X ^ 4 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z), Vec\<^sub>0 0 (Z\<^sup>2 - X - Y)])) ()) =
  [
    Vec\<^sub>0 0 1 + Vec\<^sub>0 3 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 1 1 + Vec\<^sub>0 3 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z) - Vec\<^sub>0 1 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 2 1 + Vec\<^sub>0 3 (Z\<^sup>2 - X - Y),
    Vec\<^sub>0 1 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 0 (- (Y ^ 3 * Z\<^sup>2) + Y ^ 4 + X * Y ^ 3 + 2 * X\<^sup>2 * Z + 2 * X * Y * Z - 2 * X * Z ^ 3) +
      Vec\<^sub>0 1 (X ^ 4 * Z\<^sup>2 - X ^ 5 - X ^ 4 * Y - 3 * X ^ 3 * Y - 3 * X\<^sup>2 * Y\<^sup>2 + 3 * X\<^sup>2 * Y * Z\<^sup>2)
  ]"
  by eval

lemma
  "syzygy_basis DRLEX [Vec\<^sub>0 0 (X ^ 4 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z), Vec\<^sub>0 0 (Z\<^sup>2 - X - Y)] =
  [
    Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z) - Vec\<^sub>0 1 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 1 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 0 (- (Y ^ 3 * Z\<^sup>2) + Y ^ 4 + X * Y ^ 3 + 2 * X\<^sup>2 * Z + 2 * X * Y * Z - 2 * X * Z ^ 3) +
      Vec\<^sub>0 1 (X ^ 4 * Z\<^sup>2 - X ^ 5 - X ^ 4 * Y - 3 * X ^ 3 * Y - 3 * X\<^sup>2 * Y\<^sup>2 + 3 * X\<^sup>2 * Y * Z\<^sup>2)
  ]"
  by eval

value [code] "syzygy_basis DRLEX [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)]"

lemma
  "map fst (gb_pprod (POT DRLEX) (map (\<lambda>p. (p, ())) (init_syzygy_list_pprod
    [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)])) ()) =
  [
    Vec\<^sub>0 0 1 + Vec\<^sub>0 3 (X * Y - Z),
    Vec\<^sub>0 1 1 + Vec\<^sub>0 3 (X * Z - Y),
    Vec\<^sub>0 2 1 + Vec\<^sub>0 3 (Y * Z - X),
    Vec\<^sub>0 0 (- X * Z + Y) + Vec\<^sub>0 1 (X * Y - Z),
    Vec\<^sub>0 0 (- Y * Z + X) + Vec\<^sub>0 2 (X * Y - Z),
    Vec\<^sub>0 1 (- Y * Z + X) + Vec\<^sub>0 2 (X * Z - Y),
    Vec\<^sub>0 1 (-Y) + Vec\<^sub>0 2 (X) + Vec\<^sub>0 3 (Y ^ 2 - X ^ 2),
    Vec\<^sub>0 0 (Z) + Vec\<^sub>0 2 (-X) + Vec\<^sub>0 3 (X ^ 2 - Z ^ 2),
    Vec\<^sub>0 0 (Y - Y * Z ^ 2) + Vec\<^sub>0 1 (Y ^ 2 * Z - Z) + Vec\<^sub>0 2 (Y ^ 2 - Z ^ 2),
    Vec\<^sub>0 0 (- Y) + Vec\<^sub>0 1 (- (X * Y)) + Vec\<^sub>0 2 (X ^ 2 - 1) + Vec\<^sub>0 3 (X - X ^ 3)
  ]"
  by eval

lemma
  "syzygy_basis DRLEX [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)] =
  [
    Vec\<^sub>0 0 (- X * Z + Y) + Vec\<^sub>0 1 (X * Y - Z),
    Vec\<^sub>0 0 (- Y * Z + X) + Vec\<^sub>0 2 (X * Y - Z),
    Vec\<^sub>0 1 (- Y * Z + X) + Vec\<^sub>0 2 (X * Z - Y),
    Vec\<^sub>0 0 (Y - Y * Z ^ 2) + Vec\<^sub>0 1 (Y ^ 2 * Z - Z) + Vec\<^sub>0 2 (Y ^ 2 - Z ^ 2)
  ]"
  by eval

end

end (* theory *)
