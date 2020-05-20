(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Simple operations: demotion, merging, composition\<close>

theory Composition imports
  Axiomatised_BNF_CC
begin

text \<open>
  We illustrate the composition of \BNFCC{}s with one example for each kind of parameters
  (live/co-/contravariant/fixed). We do not show demotion and merging in isolation, as the
  examples for composition use these operations, too.
\<close>

subsection \<open>Composition in a live position\<close>

type_synonym
  ('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGl =
    "(('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f1) G,
    'l1, 'l3, 'co1, 'co3, 'co4, 'contra1, 'contra3, 'contra4, 'f2) F"

text \<open>The type variables @{typ 'l1}, @{typ 'co1} and @{typ 'contra1} have each been merged.\<close>

definition "rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4 =
  rel_F (rel_G L1 L2 Co1 Co2 Contra1 Contra2) L1 L3 Co1 Co3 Co4 Contra1 Contra3 Contra4"

definition "map_FGl l1 l2 l3 co1 co2 co3 co4 contra1 contra2 contra3 contra4 =
  map_F (map_G l1 l2 co1 co2 contra1 contra2) l1 l3 co1 co3 co4 contra1 contra3 contra4"

lemma rel_FGl_mono:
  "\<lbrakk> L1 \<le> L1'; L2 \<le> L2'; L3 \<le> L3'; Co1 \<le> Co1'; Co2 \<le> Co2'; Co3 \<le> Co3'; Co4 \<le> Co4';
     Contra1' \<le> Contra1; Contra2' \<le> Contra2; Contra3' \<le> Contra3; Contra4' \<le> Contra4 \<rbrakk> \<Longrightarrow>
  rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4 \<le>
  rel_FGl L1' L2' L3' Co1' Co2' Co3' Co4' Contra1' Contra2' Contra3' Contra4'"
  unfolding rel_FGl_def
  apply (rule rel_F_mono)
          apply (rule rel_G_mono)
               apply (assumption)+
  done

lemma rel_FGl_eq: "rel_FGl (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) = (=)"
  unfolding rel_FGl_def by (simp add: rel_F_eq rel_G_eq)

lemma rel_FGl_conversep:
  "rel_FGl L1\<inverse>\<inverse> L2\<inverse>\<inverse> L3\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Co3\<inverse>\<inverse> Co4\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> Contra3\<inverse>\<inverse> Contra4\<inverse>\<inverse> =
  (rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4)\<inverse>\<inverse>"
  unfolding rel_FGl_def by (simp add: rel_F_conversep rel_G_conversep)

lemma map_FGl_id0: "map_FGl id id id id id id id id id id id = id"
  unfolding map_FGl_def by (simp add: map_F_id0 map_G_id0)

lemma map_FGl_comp: "map_FGl l1 l2 l3 co1 co2 co3 co4 contra1 contra2 contra3 contra4 \<circ>
  map_FGl l1' l2' l3' co1' co2' co3' co4' contra1' contra2' contra3' contra4' =
  map_FGl (l1 \<circ> l1') (l2 \<circ> l2') (l3 \<circ> l3') (co1 \<circ> co1') (co2 \<circ> co2') (co3 \<circ> co3') (co4 \<circ> co4')
    (contra1' \<circ> contra1) (contra2' \<circ> contra2) (contra3' \<circ> contra3) (contra4' \<circ> contra4)"
  unfolding map_FGl_def by (simp add: map_F_comp map_G_comp)

lemma map_FGl_parametric:
  "rel_fun (rel_fun L1 L1') (rel_fun (rel_fun L2 L2') (rel_fun (rel_fun L3 L3')
  (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2')
    (rel_fun (rel_fun Co3 Co3') (rel_fun (rel_fun Co4 Co4')
  (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
    (rel_fun (rel_fun Contra3' Contra3) (rel_fun (rel_fun Contra4' Contra4)
  (rel_fun (rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4)
  (rel_FGl L1' L2' L3' Co1' Co2' Co3' Co4' Contra1' Contra2' Contra3' Contra4'))))))))))))
  map_FGl map_FGl"
  unfolding rel_FGl_def map_FGl_def
  apply (intro rel_funI)
  apply (elim map_F_rel_cong map_G_rel_cong)
               apply (erule (2) rel_funE)+
  done

definition rel_FGl_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool"
  where
  "rel_FGl_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool)
    (L3 :: 'l3 \<Rightarrow> 'l3' \<Rightarrow> bool) (L3' :: 'l3' \<Rightarrow> 'l3'' \<Rightarrow> bool).
    (rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGl \<Rightarrow> _) OO
      rel_FGl L1' L2' L3' Co1' Co2' Co3' Co4' Contra1' Contra2' Contra3' Contra4' \<le>
    rel_FGl (L1 OO L1') (L2 OO L2') (L3 OO L3') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3') (Co4 OO Co4')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') (Contra4 OO Contra4'))"

definition rel_FGl_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool"
  where
  "rel_FGl_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool)
    (L3 :: 'l3 \<Rightarrow> 'l3' \<Rightarrow> bool) (L3' :: 'l3' \<Rightarrow> 'l3'' \<Rightarrow> bool).
    rel_FGl (L1 OO L1') (L2 OO L2') (L3 OO L3')
      (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3') (Co4 OO Co4')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') (Contra4 OO Contra4') \<le>
    (rel_FGl L1 L2 L3 Co1 Co2 Co3 Co4 Contra1 Contra2 Contra3 Contra4 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGl \<Rightarrow> _) OO
      rel_FGl L1' L2' L3' Co1' Co2' Co3' Co4' Contra1' Contra2' Contra3' Contra4')"

text \<open>Sufficient conditions for subdistributivity over relation composition.\<close>

lemma rel_FGl_pos_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_F :: "(('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f1) G \<times>
      ('l1', 'l2', 'co1', 'co2', 'contra1', 'contra2', 'f1) G \<times>
      ('l1'', 'l2'', 'co1'', 'co2'', 'contra1'', 'contra2'', 'f1) G \<times>
      'l1 \<times> 'l1' \<times> 'l1'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f2) itself"
    and tytok_G :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f1) itself"
    and tytok_FGl :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times>
      'f1 \<times> 'f2) itself"
  assumes "rel_F_pos_distr_cond Co1 Co1' Co3 Co3' Co4 Co4'
      Contra1 Contra1' Contra3 Contra3' Contra4 Contra4' tytok_F"
    and "rel_G_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_G"
  shows "rel_FGl_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' tytok_FGl"
  unfolding rel_FGl_pos_distr_cond_def rel_FGl_def
  apply (intro allI)
  apply (rule order_trans)
   apply (rule rel_F_pos_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule rel_G_pos_distr)
          apply (rule assms(2))
         apply (rule order_refl)+
  done

lemma rel_FGl_neg_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_F :: "(('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f1) G \<times>
      ('l1', 'l2', 'co1', 'co2', 'contra1', 'contra2', 'f1) G \<times>
      ('l1'', 'l2'', 'co1'', 'co2'', 'contra1'', 'contra2'', 'f1) G \<times>
      'l1 \<times> 'l1' \<times> 'l1'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f2) itself"
    and tytok_G :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f1) itself"
    and tytok_FGl :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times>
      'f1 \<times> 'f2) itself"
  assumes "rel_F_neg_distr_cond Co1 Co1' Co3 Co3' Co4 Co4'
      Contra1 Contra1' Contra3 Contra3' Contra4 Contra4' tytok_F"
    and "rel_G_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_G"
  shows "rel_FGl_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' tytok_FGl"
  unfolding rel_FGl_neg_distr_cond_def rel_FGl_def
  apply (intro allI)
  apply (rule order_trans[rotated])
   apply (rule rel_F_neg_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule rel_G_neg_distr)
          apply (rule assms(2))
         apply (rule order_refl)+
  done

lemma rel_FGl_pos_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times>
    'f1 \<times> 'f2) itself"
  shows "rel_FGl_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  by (rule rel_FGl_pos_distr_imp rel_F_pos_distr_cond_eq rel_G_pos_distr_cond_eq)+

lemma rel_FGl_neg_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times>
    'f1 \<times> 'f2) itself"
  shows "rel_FGl_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  by (rule rel_FGl_neg_distr_imp rel_F_neg_distr_cond_eq rel_G_neg_distr_cond_eq)+

definition "rell_FGl L1 L2 L3 = rel_FGl L1 L2 L3 (=) (=) (=) (=) (=) (=) (=) (=)"
definition "mapl_FGl l1 l2 l3 = map_FGl l1 l2 l3 id id id id id id id id"

type_synonym ('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGlbd =
  "('co1, 'co3, 'co4, 'contra1, 'contra3, 'contra4, 'f2) Fbd \<times>
    ('co1, 'co2, 'contra1, 'contra2, 'f1) Gbd +
    ('co1, 'co3, 'co4, 'contra1, 'contra3, 'contra4, 'f2) Fbd"

definition set1_FGl :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'co4,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGl \<Rightarrow> 'l1 set" where
  "set1_FGl x = (\<Union>y\<in>set1_F x. set1_G y) \<union> set2_F x"

definition set2_FGl :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'co4,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGl \<Rightarrow> 'l2 set" where
  "set2_FGl x = (\<Union>y\<in>set1_F x. set2_G y)"

definition set3_FGl :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'co4,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGl \<Rightarrow> 'l3 set" where
  "set3_FGl x = set3_F x"

definition
  bd_FGl :: "('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGlbd rel"
  where "bd_FGl = bd_F *c bd_G +c bd_F"

lemma set1_FGl_map: "set1_FGl \<circ> mapl_FGl l1 l2 l3 = image l1 \<circ> set1_FGl"
  by (simp add: fun_eq_iff set1_FGl_def mapl_FGl_def map_FGl_def
      mapl_F_def[symmetric] mapl_G_def[symmetric]
      set1_F_map[THEN fun_cong, simplified] set2_F_map[THEN fun_cong, simplified]
      set1_G_map[THEN fun_cong, simplified]
      image_Un image_UN)

lemma set2_FGl_map: "set2_FGl \<circ> mapl_FGl l1 l2 l3 = image l2 \<circ> set2_FGl"
  by (simp add: fun_eq_iff set2_FGl_def mapl_FGl_def map_FGl_def
      mapl_F_def[symmetric] mapl_G_def[symmetric]
      set1_F_map[THEN fun_cong, simplified] set2_G_map[THEN fun_cong, simplified] image_UN)

lemma set3_FGl_map: "set3_FGl \<circ> mapl_FGl l1 l2 l3 = image l3 \<circ> set3_FGl"
  by (simp add: fun_eq_iff set3_FGl_def mapl_FGl_def map_FGl_def
      mapl_F_def[symmetric] mapl_G_def[symmetric] set3_F_map[THEN fun_cong, simplified])

lemma bd_FGl_card_order: "card_order bd_FGl"
  unfolding bd_FGl_def using bd_F_card_order bd_G_card_order
  by (intro card_order_csum card_order_cprod)

lemma bd_FGl_cinfinite: "cinfinite bd_FGl"
  unfolding bd_FGl_def using bd_F_cinfinite bd_G_cinfinite
  by (intro cinfinite_csum disjI2)

lemma
  fixes x :: "(_, _, _, 'co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGl"
  shows set1_FGl_bound: "card_of (set1_FGl x) \<le>o
      (bd_FGl :: ('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGlbd rel)"
    and set2_FGl_bound: "card_of (set2_FGl x) \<le>o
      (bd_FGl :: ('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGlbd rel)"
    and set3_FGl_bound: "card_of (set3_FGl x) \<le>o
      (bd_FGl :: ('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGlbd rel)"
  unfolding set1_FGl_def set2_FGl_def set3_FGl_def bd_FGl_def
    apply (simp)
    apply (rule ordLeq_transitive)
     apply (rule Un_csum)
    apply (rule csum_mono)
     apply (rule comp_single_set_bd[where fset=set1_G and gset=set1_F, rotated])
       apply (rule set1_G_bound)
      apply (rule set1_F_bound)
     apply (rule card_order_on_Card_order[THEN conjunct2, OF bd_G_card_order])
    apply (rule set2_F_bound)
   apply (rule ordLeq_transitive)
    apply (rule comp_single_set_bd[where fset=set2_G and gset=set1_F, rotated])
      apply (rule set2_G_bound)
     apply (rule set1_F_bound)
    apply (rule card_order_on_Card_order[THEN conjunct2, OF bd_G_card_order])
   apply (rule ordLeq_csum1)
   apply (rule Card_order_cprod)
  apply (rule ordLeq_transitive)
   apply (rule set3_F_bound)
  apply (rule ordLeq_csum2)
  apply (rule card_order_on_Card_order[THEN conjunct2, OF bd_F_card_order])
  done

lemma mapl_FGl_cong:
  assumes "\<And>z. z \<in> set1_FGl x \<Longrightarrow> l1 z = l1' z" and "\<And>z. z \<in> set2_FGl x \<Longrightarrow> l2 z = l2' z"
    and "\<And>z. z \<in> set3_FGl x \<Longrightarrow> l3 z = l3' z"
  shows "mapl_FGl l1 l2 l3 x = mapl_FGl l1' l2' l3' x"
  unfolding mapl_FGl_def map_FGl_def mapl_G_def[symmetric] mapl_F_def[symmetric]
  by (auto 0 5 intro: mapl_F_cong mapl_G_cong assms simp add: set1_FGl_def set2_FGl_def set3_FGl_def)

lemma rell_FGl_mono_strong:
  assumes "rell_FGl L1 L2 L3 x y"
    and "\<And>a b. a \<in> set1_FGl x \<Longrightarrow> b \<in> set1_FGl y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b"
    and "\<And>a b. a \<in> set2_FGl x \<Longrightarrow> b \<in> set2_FGl y \<Longrightarrow> L2 a b \<Longrightarrow> L2' a b"
    and "\<And>a b. a \<in> set3_FGl x \<Longrightarrow> b \<in> set3_FGl y \<Longrightarrow> L3 a b \<Longrightarrow> L3' a b"
  shows "rell_FGl L1' L2' L3' x y"
  using assms(1) unfolding rell_FGl_def rel_FGl_def rell_G_def[symmetric] rell_F_def[symmetric]
  by (auto 0 5 intro: rell_F_mono_strong rell_G_mono_strong assms(2-4)
      simp add: set1_FGl_def set2_FGl_def set3_FGl_def)


subsection \<open>Composition in a covariant position\<close>

type_synonym
  ('l1, 'co1, 'co2, 'co3, 'co4, 'co5, 'co6, 'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGco =
    "('l1, 'co1, 'co5, ('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'f1) G, 'co3, 'co6,
    'contra1, 'contra3, 'contra4, 'f2) F"

text \<open>The type variables @{typ 'co1}, @{typ 'co3} and @{typ 'contra1} have each been merged.\<close>

definition "rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4 =
  rel_F L1 Co1 Co5 (rel_G Co1 Co2 Co3 Co4 Contra1 Contra2) Co3 Co6 Contra1 Contra3 Contra4"

definition "map_FGco l1 co1 co2 co3 co4 co5 co6 contra1 contra2 contra3 contra4 =
  map_F l1 co1 co5 (map_G co1 co2 co3 co4 contra1 contra2) co3 co6 contra1 contra3 contra4"

lemma rel_FGco_mono:
  "\<lbrakk> L1 \<le> L1'; Co1 \<le> Co1'; Co2 \<le> Co2'; Co3 \<le> Co3'; Co4 \<le> Co4'; Co5 \<le> Co5'; Co6 \<le> Co6';
     Contra1' \<le> Contra1; Contra2' \<le> Contra2; Contra3' \<le> Contra3; Contra4' \<le> Contra4 \<rbrakk> \<Longrightarrow>
  rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4 \<le>
  rel_FGco L1' Co1' Co2' Co3' Co4' Co5' Co6' Contra1' Contra2' Contra3' Contra4'"
  unfolding rel_FGco_def
  apply (rule rel_F_mono)
          apply (assumption)+
       apply (rule rel_G_mono)
            apply (assumption)+
  done

lemma rel_FGco_eq: "rel_FGco (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) = (=)"
  unfolding rel_FGco_def by (simp add: rel_F_eq rel_G_eq)

lemma rel_FGco_conversep:
  "rel_FGco L1\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Co3\<inverse>\<inverse> Co4\<inverse>\<inverse> Co5\<inverse>\<inverse> Co6\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> Contra3\<inverse>\<inverse> Contra4\<inverse>\<inverse> =
  (rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4)\<inverse>\<inverse>"
  unfolding rel_FGco_def by (simp add: rel_F_conversep rel_G_conversep)

lemma map_FGco_id0: "map_FGco id id id id id id id id id id id = id"
  unfolding map_FGco_def by (simp add: map_F_id0 map_G_id0)

lemma map_FGco_comp: "map_FGco l1 co1 co2 co3 co4 co5 co6 contra1 contra2 contra3 contra4 \<circ>
  map_FGco l1' co1' co2' co3' co4' co5' co6' contra1' contra2' contra3' contra4' =
  map_FGco (l1 \<circ> l1') (co1 \<circ> co1') (co2 \<circ> co2') (co3 \<circ> co3') (co4 \<circ> co4') (co5 \<circ> co5') (co6 \<circ> co6')
    (contra1' \<circ> contra1) (contra2' \<circ> contra2) (contra3' \<circ> contra3) (contra4' \<circ> contra4)"
  unfolding map_FGco_def by (simp add: map_F_comp map_G_comp)

lemma map_FGco_parametric:
  "rel_fun (rel_fun L1 L1') (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2')
    (rel_fun (rel_fun Co3 Co3') (rel_fun (rel_fun Co4 Co4')
    (rel_fun (rel_fun Co5 Co5') (rel_fun (rel_fun Co6 Co6')
  (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
    (rel_fun (rel_fun Contra3' Contra3) (rel_fun (rel_fun Contra4' Contra4)
  (rel_fun (rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4)
  (rel_FGco L1' Co1' Co2' Co3' Co4' Co5' Co6' Contra1' Contra2' Contra3' Contra4'))))))))))))
  map_FGco map_FGco"
  unfolding rel_FGco_def map_FGco_def
  apply (intro rel_funI)
  apply (elim map_F_rel_cong map_G_rel_cong)
               apply (erule (2) rel_funE)+
  done

definition rel_FGco_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('co5 \<Rightarrow> 'co5' \<Rightarrow> bool) \<Rightarrow> ('co5' \<Rightarrow> 'co5'' \<Rightarrow> bool) \<Rightarrow>
    ('co6 \<Rightarrow> 'co6' \<Rightarrow> bool) \<Rightarrow> ('co6' \<Rightarrow> 'co6'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool" where
  "rel_FGco_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5' Co6 Co6'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool).
    (rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGco \<Rightarrow> _) OO
      rel_FGco L1' Co1' Co2' Co3' Co4' Co5' Co6' Contra1' Contra2' Contra3' Contra4' \<le>
    rel_FGco (L1 OO L1') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
      (Co4 OO Co4') (Co5 OO Co5') (Co6 OO Co6')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') (Contra4 OO Contra4'))"

definition rel_FGco_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('co5 \<Rightarrow> 'co5' \<Rightarrow> bool) \<Rightarrow> ('co5' \<Rightarrow> 'co5'' \<Rightarrow> bool) \<Rightarrow>
    ('co6 \<Rightarrow> 'co6' \<Rightarrow> bool) \<Rightarrow> ('co6' \<Rightarrow> 'co6'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool" where
  "rel_FGco_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5' Co6 Co6'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool).
    rel_FGco (L1 OO L1') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
      (Co4 OO Co4') (Co5 OO Co5') (Co6 OO Co6')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') (Contra4 OO Contra4') \<le>
    (rel_FGco L1 Co1 Co2 Co3 Co4 Co5 Co6 Contra1 Contra2 Contra3 Contra4 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGco \<Rightarrow> _) OO
      rel_FGco L1' Co1' Co2' Co3' Co4' Co5' Co6' Contra1' Contra2' Contra3' Contra4')"

text \<open>Sufficient conditions for subdistributivity over relation composition.\<close>

lemma rel_FGco_pos_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Co5 :: "'co5 \<Rightarrow> 'co5' \<Rightarrow> bool" and Co5' :: "'co5' \<Rightarrow> 'co5'' \<Rightarrow> bool"
    and tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'co1 \<times> 'co1' \<times> 'co1'' \<times> 'co5 \<times> 'co5' \<times> 'co5'' \<times>
      'f2) itself"
    and tytok_G :: "('co1 \<times> 'co1' \<times> 'co1'' \<times> 'co2 \<times> 'co2' \<times> 'co2'' \<times> 'f1) itself"
    and tytok_FGco :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  assumes "rel_F_pos_distr_cond
      (rel_G Co1 Co2 Co3 Co4 Contra1 Contra2 :: (_, _, _, _, _, _, 'f1) G \<Rightarrow> _)
      (rel_G Co1' Co2' Co3' Co4' Contra1' Contra2') Co3 Co3' Co6 Co6'
      Contra1 Contra1' Contra3 Contra3' Contra4 Contra4' tytok_F"
    and "rel_G_pos_distr_cond Co3 Co3' Co4 Co4' Contra1 Contra1' Contra2 Contra2' tytok_G"
  shows "rel_FGco_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5' Co6 Co6'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' tytok_FGco"
  unfolding rel_FGco_pos_distr_cond_def rel_FGco_def
  apply (intro allI)
  apply (rule order_trans)
   apply (rule rel_F_pos_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule order_refl)+
       apply (rule rel_G_pos_distr)
       apply (rule assms(2))
      apply (rule order_refl)+
  done

lemma rel_FGco_neg_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Co5 :: "'co5 \<Rightarrow> 'co5' \<Rightarrow> bool" and Co5' :: "'co5' \<Rightarrow> 'co5'' \<Rightarrow> bool"
    and tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'co1 \<times> 'co1' \<times> 'co1'' \<times> 'co5 \<times> 'co5' \<times> 'co5'' \<times> 'f2) itself"
    and tytok_G :: "('co1 \<times> 'co1' \<times> 'co1'' \<times> 'co2 \<times> 'co2' \<times> 'co2'' \<times> 'f1) itself"
    and tytok_FGco :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  assumes "rel_F_neg_distr_cond
      (rel_G Co1 Co2 Co3 Co4 Contra1 Contra2 :: (_, _, _, _, _, _, 'f1) G \<Rightarrow> _)
      (rel_G Co1' Co2' Co3' Co4' Contra1' Contra2') Co3 Co3' Co6 Co6'
      Contra1 Contra1' Contra3 Contra3' Contra4 Contra4' tytok_F"
    and "rel_G_neg_distr_cond Co3 Co3' Co4 Co4' Contra1 Contra1' Contra2 Contra2' tytok_G"
  shows "rel_FGco_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5' Co6 Co6'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' tytok_FGco"
  unfolding rel_FGco_neg_distr_cond_def rel_FGco_def
  apply (intro allI)
  apply (rule order_trans[rotated])
   apply (rule rel_F_neg_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule order_refl)+
       apply (rule rel_G_neg_distr)
       apply (rule assms(2))
      apply (rule order_refl)+
  done

lemma rel_FGco_pos_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  shows "rel_FGco_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  apply (rule rel_FGco_pos_distr_imp)
   apply (simp add: rel_G_eq)
   apply (rule rel_F_pos_distr_cond_eq rel_G_pos_distr_cond_eq)+
  done

lemma rel_FGco_neg_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  shows "rel_FGco_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  apply (rule rel_FGco_neg_distr_imp)
   apply (simp add: rel_G_eq)
   apply (rule rel_F_neg_distr_cond_eq rel_G_neg_distr_cond_eq)+
  done

definition "rell_FGco L1 = rel_FGco L1 (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)"
definition "mapl_FGco l1 = map_FGco l1 id id id id id id id id id id"

type_synonym ('co1, 'co2, 'co3, 'co4, 'co5, 'co6,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGcobd =
  "(('co1, 'co2, 'co3, 'co4, 'contra1, 'contra2, 'f1) G,
    'co3, 'co6, 'contra1, 'contra3, 'contra4, 'f2) Fbd"

definition set1_FGco :: "('l1, 'co1, 'co2, 'co3, 'co4, 'co5, 'co6,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGco \<Rightarrow> 'l1 set" where
  "set1_FGco x = set1_F x"

definition bd_FGco :: "('co1, 'co2, 'co3, 'co4, 'co5, 'co6,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGcobd rel" where
  "bd_FGco = bd_F"

lemma set1_FGco_map: "set1_FGco \<circ> mapl_FGco l1 = image l1 \<circ> set1_FGco"
  by (simp add: fun_eq_iff set1_FGco_def mapl_FGco_def map_FGco_def
      mapl_F_def[symmetric] mapl_G_def[symmetric] mapl_G_id0
      set1_F_map[THEN fun_cong, simplified])

lemma bd_FGco_card_order: "card_order bd_FGco"
  unfolding bd_FGco_def using bd_F_card_order .

lemma bd_FGco_cinfinite: "cinfinite bd_FGco"
  unfolding bd_FGco_def using bd_F_cinfinite .

lemma set1_FGco_bound:
  fixes x :: "(_, 'co1, 'co2, 'co3, 'co4, 'co5, 'co6,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGco"
  shows "card_of (set1_FGco x) \<le>o (bd_FGco :: ('co1, 'co2, 'co3, 'co4, 'co5, 'co6,
    'contra1, 'contra2, 'contra3, 'contra4, 'f1, 'f2) FGcobd rel)"
  unfolding set1_FGco_def bd_FGco_def using set1_F_bound .

lemma mapl_FGco_cong:
  assumes "\<And>z. z \<in> set1_FGco x \<Longrightarrow> l1 z = l1' z"
  shows "mapl_FGco l1 x = mapl_FGco l1' x"
  unfolding mapl_FGco_def map_FGco_def mapl_G_def[symmetric] mapl_F_def[symmetric] mapl_G_id0
  by (auto 0 3 intro: mapl_F_cong assms simp add: set1_FGco_def)

lemma rell_FGco_mono_strong:
  assumes "rell_FGco L1 x y"
    and "\<And>a b. a \<in> set1_FGco x \<Longrightarrow> b \<in> set1_FGco y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b"
  shows "rell_FGco L1' x y"
  using assms(1) unfolding rell_FGco_def rel_FGco_def rel_G_eq rell_F_def[symmetric]
  by (auto 0 3 intro: rell_F_mono_strong assms(2) simp add: set1_FGco_def)


subsection \<open>Composition in a contravariant position\<close>

type_synonym
  ('l1, 'co1, 'co2, 'co3, 'co4, 'co5, 'contra1,
    'contra2, 'contra3, 'contra4, 'contra5, 'f1, 'f2) FGcontra =
  "('l1, 'co1, 'co3, 'co1, 'co4, 'co5, ('contra1, 'contra2, 'contra3, 'contra4, 'co1, 'co2, 'f1) G,
    'contra1, 'contra5, 'f2) F"

text \<open>The type variables @{typ 'co1} and @{typ 'contra1} have each been merged.\<close>

definition "rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5 =
  rel_F L1 Co1 Co3 Co1 Co4 Co5 (rel_G Contra1 Contra2 Contra3 Contra4 Co1 Co2) Contra1 Contra5"

definition "map_FGcontra l1 co1 co2 co3 co4 co5 contra1 contra2 contra3 contra4 contra5 =
  map_F l1 co1 co3 co1 co4 co5 (map_G contra1 contra2 contra3 contra4 co1 co2) contra1 contra5"

lemma rel_FGcontra_mono:
  "\<lbrakk> L1 \<le> L1'; Co1 \<le> Co1'; Co2 \<le> Co2'; Co3 \<le> Co3'; Co4 \<le> Co4'; Co5 \<le> Co5';
     Contra1' \<le> Contra1; Contra2' \<le> Contra2; Contra3' \<le> Contra3;
     Contra4' \<le> Contra4; Contra5' \<le> Contra5 \<rbrakk> \<Longrightarrow>
  rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5 \<le>
  rel_FGcontra L1' Co1' Co2' Co3' Co4' Co5' Contra1' Contra2' Contra3' Contra4' Contra5'"
  unfolding rel_FGcontra_def
  apply (rule rel_F_mono)
          apply (assumption)+
    apply (rule rel_G_mono)
         apply (assumption)+
  done

lemma rel_FGcontra_eq: "rel_FGcontra (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) = (=)"
  unfolding rel_FGcontra_def by (simp add: rel_F_eq rel_G_eq)

lemma rel_FGcontra_conversep:
  "rel_FGcontra L1\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Co3\<inverse>\<inverse> Co4\<inverse>\<inverse> Co5\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> Contra3\<inverse>\<inverse> Contra4\<inverse>\<inverse> Contra5\<inverse>\<inverse> =
  (rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5)\<inverse>\<inverse>"
  unfolding rel_FGcontra_def by (simp add: rel_F_conversep rel_G_conversep)

lemma map_FGcontra_id0: "map_FGcontra id id id id id id id id id id id = id"
  unfolding map_FGcontra_def by (simp add: map_F_id0 map_G_id0)

lemma map_FGcontra_comp:
  "map_FGcontra l1 co1 co2 co3 co4 co5 contra1 contra2 contra3 contra4 contra5 \<circ>
  map_FGcontra l1' co1' co2' co3' co4' co5' contra1' contra2' contra3' contra4' contra5' =
  map_FGcontra (l1 \<circ> l1') (co1 \<circ> co1') (co2 \<circ> co2') (co3 \<circ> co3') (co4 \<circ> co4') (co5 \<circ> co5')
    (contra1' \<circ> contra1) (contra2' \<circ> contra2) (contra3' \<circ> contra3)
    (contra4' \<circ> contra4) (contra5' \<circ> contra5)"
  unfolding map_FGcontra_def by (simp add: map_F_comp map_G_comp)

lemma map_FGcontra_parametric:
  "rel_fun (rel_fun L1 L1') (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2')
    (rel_fun (rel_fun Co3 Co3') (rel_fun (rel_fun Co4 Co4') (rel_fun (rel_fun Co5 Co5')
  (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
    (rel_fun (rel_fun Contra3' Contra3) (rel_fun (rel_fun Contra4' Contra4)
    (rel_fun (rel_fun Contra5' Contra5)
  (rel_fun (rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5)
  (rel_FGcontra L1' Co1' Co2' Co3' Co4' Co5' Contra1' Contra2' Contra3' Contra4' Contra5'))))))))))))
  map_FGcontra map_FGcontra"
  unfolding rel_FGcontra_def map_FGcontra_def
  apply (intro rel_funI)
  apply (elim map_F_rel_cong map_G_rel_cong)
               apply (erule (2) rel_funE)+
  done

definition rel_FGcontra_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('co5 \<Rightarrow> 'co5' \<Rightarrow> bool) \<Rightarrow> ('co5' \<Rightarrow> 'co5'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('contra5 \<Rightarrow> 'contra5' \<Rightarrow> bool) \<Rightarrow> ('contra5' \<Rightarrow> 'contra5'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool" where
  "rel_FGcontra_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' Contra5 Contra5' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool).
    (rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGcontra \<Rightarrow> _) OO
      rel_FGcontra L1' Co1' Co2' Co3' Co4' Co5' Contra1' Contra2' Contra3' Contra4' Contra5' \<le>
    rel_FGcontra (L1 OO L1') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3') (Co4 OO Co4') (Co5 OO Co5')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3')
      (Contra4 OO Contra4') (Contra5 OO Contra5'))"

definition rel_FGcontra_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('co4 \<Rightarrow> 'co4' \<Rightarrow> bool) \<Rightarrow> ('co4' \<Rightarrow> 'co4'' \<Rightarrow> bool) \<Rightarrow>
    ('co5 \<Rightarrow> 'co5' \<Rightarrow> bool) \<Rightarrow> ('co5' \<Rightarrow> 'co5'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra4 \<Rightarrow> 'contra4' \<Rightarrow> bool) \<Rightarrow> ('contra4' \<Rightarrow> 'contra4'' \<Rightarrow> bool) \<Rightarrow>
    ('contra5 \<Rightarrow> 'contra5' \<Rightarrow> bool) \<Rightarrow> ('contra5' \<Rightarrow> 'contra5'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself \<Rightarrow> bool" where
  "rel_FGcontra_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' Contra5 Contra5' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool).
    rel_FGcontra (L1 OO L1') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3') (Co4 OO Co4') (Co5 OO Co5')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3')
      (Contra4 OO Contra4') (Contra5 OO Contra5') \<le>
    (rel_FGcontra L1 Co1 Co2 Co3 Co4 Co5 Contra1 Contra2 Contra3 Contra4 Contra5 ::
      (_, _, _, _, _, _, _, _, _, _, _, 'f1, 'f2) FGcontra \<Rightarrow> _) OO
      rel_FGcontra L1' Co1' Co2' Co3' Co4' Co5' Contra1' Contra2' Contra3' Contra4' Contra5')"

text \<open>Sufficient conditions for subdistributivity over relation composition.\<close>

lemma rel_FGcontra_pos_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co3 :: "'co3 \<Rightarrow> 'co3' \<Rightarrow> bool" and Co3' :: "'co3' \<Rightarrow> 'co3'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'co1 \<times> 'co1' \<times> 'co1'' \<times> 'co3 \<times> 'co3' \<times> 'co3'' \<times>
      'f2) itself"
    and tytok_G :: "('contra1 \<times> 'contra1' \<times> 'contra1'' \<times> 'contra2 \<times> 'contra2' \<times> 'contra2'' \<times>
      'f1) itself"
    and tytok_FGcontra :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  assumes "rel_F_pos_distr_cond Co1 Co1' Co4 Co4' Co5 Co5'
      (rel_G Contra1 Contra2 Contra3 Contra4 Co1 Co2 :: (_, _, _, _, _, _, 'f1) G \<Rightarrow> _)
      (rel_G Contra1' Contra2' Contra3' Contra4' Co1' Co2')
      Contra1 Contra1' Contra5 Contra5' tytok_F"
    and "rel_G_neg_distr_cond Contra3 Contra3' Contra4 Contra4' Co1 Co1' Co2 Co2' tytok_G"
  shows "rel_FGcontra_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' Contra5 Contra5'
    tytok_FGcontra"
  unfolding rel_FGcontra_pos_distr_cond_def rel_FGcontra_def
  apply (intro allI)
  apply (rule order_trans)
   apply (rule rel_F_pos_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule order_refl)+
    apply (rule rel_G_neg_distr)
    apply (rule assms(2))
   apply (rule order_refl)+
  done

lemma rel_FGcontra_neg_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co3 :: "'co3 \<Rightarrow> 'co3' \<Rightarrow> bool" and Co3' :: "'co3' \<Rightarrow> 'co3'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'co1 \<times> 'co1' \<times> 'co1'' \<times> 'co3 \<times> 'co3' \<times> 'co3'' \<times>
      'f2) itself"
    and tytok_G :: "('contra1 \<times> 'contra1' \<times> 'contra1'' \<times> 'contra2 \<times> 'contra2' \<times> 'contra2'' \<times>
      'f1) itself"
    and tytok_FGcontra :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  assumes "rel_F_neg_distr_cond Co1 Co1' Co4 Co4' Co5 Co5'
      (rel_G Contra1 Contra2 Contra3 Contra4 Co1 Co2 :: (_, _, _, _, _, _, 'f1) G \<Rightarrow> _)
      (rel_G Contra1' Contra2' Contra3' Contra4' Co1' Co2')
      Contra1 Contra1' Contra5 Contra5' tytok_F"
    and "rel_G_pos_distr_cond Contra3 Contra3' Contra4 Contra4' Co1 Co1' Co2 Co2' tytok_G"
  shows "rel_FGcontra_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3' Co4 Co4' Co5 Co5'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' Contra4 Contra4' Contra5 Contra5' tytok_FGcontra"
  unfolding rel_FGcontra_neg_distr_cond_def rel_FGcontra_def
  apply (intro allI)
  apply (rule order_trans[rotated])
   apply (rule rel_F_neg_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (rule order_refl)+
    apply (rule rel_G_pos_distr)
    apply (rule assms(2))
   apply (rule order_refl)+
  done

lemma rel_FGcontra_pos_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  shows "rel_FGcontra_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  apply (rule rel_FGcontra_pos_distr_imp)
   apply (simp add: rel_G_eq)
   apply (rule rel_F_pos_distr_cond_eq rel_G_neg_distr_cond_eq)+
  done

lemma rel_FGcontra_neg_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'f1 \<times> 'f2) itself"
  shows "rel_FGcontra_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)
    (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  apply (rule rel_FGcontra_neg_distr_imp)
   apply (simp add: rel_G_eq)
   apply (rule rel_F_neg_distr_cond_eq rel_G_pos_distr_cond_eq)+
  done

definition "rell_FGcontra L1 = rel_FGcontra L1 (=) (=) (=) (=) (=) (=) (=) (=) (=) (=)"
definition "mapl_FGcontra l1 = map_FGcontra l1 id id id id id id id id id id"

type_synonym ('co1, 'co2, 'co3, 'co4, 'co5, 'contra1, 'contra2, 'contra3, 'contra4, 'contra5,
    'f1, 'f2) FGcontrabd =
  "('co1, 'co4, 'co5, ('contra1, 'contra2, 'contra3, 'contra4, 'co1, 'co2, 'f1) G,
    'contra1, 'contra5, 'f2) Fbd"

definition set1_FGcontra :: "('l1, 'co1, 'co2, 'co3, 'co4, 'co5,
    'contra1, 'contra2, 'contra3, 'contra4, 'contra5, 'f1, 'f2) FGcontra \<Rightarrow> 'l1 set" where
  "set1_FGcontra x = set1_F x"

definition bd_FGcontra :: "('co1, 'co2, 'co3, 'co4, 'co5,
    'contra1, 'contra2, 'contra3, 'contra4, 'contra5, 'f1, 'f2) FGcontrabd rel" where
  "bd_FGcontra = bd_F"

lemma set1_FGcontra_map: "set1_FGcontra \<circ> mapl_FGcontra l1 = image l1 \<circ> set1_FGcontra"
  by (simp add: fun_eq_iff set1_FGcontra_def mapl_FGcontra_def map_FGcontra_def
      mapl_F_def[symmetric] mapl_G_def[symmetric] mapl_G_id0
      set1_F_map[THEN fun_cong, simplified])

lemma bd_FGcontra_card_order: "card_order bd_FGcontra"
  unfolding bd_FGcontra_def using bd_F_card_order .

lemma bd_FGcontra_cinfinite: "cinfinite bd_FGcontra"
  unfolding bd_FGcontra_def using bd_F_cinfinite .

lemma set1_FGcontra_bound:
  fixes x :: "(_, 'co1, 'co2, 'co3, 'co4, 'co5,
    'contra1, 'contra2, 'contra3, 'contra4, 'contra5, 'f1, 'f2) FGcontra"
  shows "card_of (set1_FGcontra x) \<le>o (bd_FGcontra :: ('co1, 'co2, 'co3, 'co4, 'co5,
    'contra1, 'contra2, 'contra3, 'contra4, 'contra5, 'f1, 'f2) FGcontrabd rel)"
  unfolding set1_FGcontra_def bd_FGcontra_def using set1_F_bound .

lemma mapl_FGcontra_contrang:
  assumes "\<And>z. z \<in> set1_FGcontra x \<Longrightarrow> l1 z = l1' z"
  shows "mapl_FGcontra l1 x = mapl_FGcontra l1' x"
  unfolding mapl_FGcontra_def map_FGcontra_def mapl_G_def[symmetric] mapl_F_def[symmetric] mapl_G_id0
  by (auto 0 3 intro: mapl_F_cong assms simp add: set1_FGcontra_def)

lemma rell_FGcontra_mono_strong:
  assumes "rell_FGcontra L1 x y"
    and "\<And>a b. a \<in> set1_FGcontra x \<Longrightarrow> b \<in> set1_FGcontra y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b"
  shows "rell_FGcontra L1' x y"
  using assms(1) unfolding rell_FGcontra_def rel_FGcontra_def rel_G_eq rell_F_def[symmetric]
  by (auto 0 3 intro: rell_F_mono_strong assms(2) simp add: set1_FGcontra_def)


subsection \<open>Composition in a fixed position\<close>

type_synonym ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf =
  "('l1, 'l2, 'f2, 'co1, 'co2, 'f4, 'contra1, 'contra2, 'f6, ('f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) G) F"

text \<open>The type variables @{typ 'f2}, @{typ 'f4} and @{typ 'f6} have each been merged.\<close>

definition "rel_FGf L1 L2 Co1 Co2 Contra1 Contra2 =
  rel_F L1 L2 (=) Co1 Co2 (=) Contra1 Contra2 (=)"

definition "map_FGf l1 l2 co1 co2 contra1 contra2 = map_F l1 l2 id co1 co2 id contra1 contra2 id"

lemma rel_FGf_mono:
  "\<lbrakk> L1 \<le> L1'; L2 \<le> L2'; Co1 \<le> Co1'; Co2 \<le> Co2'; Contra1' \<le> Contra1; Contra2' \<le> Contra2 \<rbrakk> \<Longrightarrow>
  rel_FGf L1 L2 Co1 Co2 Contra1 Contra2 \<le> rel_FGf L1' L2' Co1' Co2' Contra1' Contra2'"
  unfolding rel_FGf_def by (rule rel_F_mono) (auto)

lemma rel_FGf_eq: "rel_FGf (=) (=) (=) (=) (=) (=) = (=)"
  unfolding rel_FGf_def by (simp add: rel_F_eq)

lemma rel_FGf_conversep:
  "rel_FGf L1\<inverse>\<inverse> L2\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> = (rel_FGf L1 L2 Co1 Co2 Contra1 Contra2)\<inverse>\<inverse>"
  unfolding rel_FGf_def by (simp add: rel_F_conversep[symmetric])

lemma map_FGf_id0: "map_FGf id id id id id id = id"
  unfolding map_FGf_def by (simp add: map_F_id0)

lemma map_FGf_comp: "map_FGf l1 l2 co1 co2 contra1 contra2 \<circ>
  map_FGf l1' l2' co1' co2' contra1' contra2' =
  map_FGf (l1 \<circ> l1') (l2 \<circ> l2') (co1 \<circ> co1') (co2 \<circ> co2') (contra1' \<circ> contra1) (contra2' \<circ> contra2)"
  unfolding map_FGf_def by (simp add: map_F_comp)

lemma map_FGf_parametric:
  "rel_fun (rel_fun L1 L1') (rel_fun (rel_fun L2 L2')
    (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2')
  (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
  (rel_fun (rel_FGf L1 L2 Co1 Co2 Contra1 Contra2)
  (rel_FGf L1' L2' Co1' Co2' Contra1' Contra2')))))))
  map_FGf map_FGf"
  unfolding rel_FGf_def map_FGf_def
  apply (intro rel_funI)
  apply (elim map_F_rel_cong)
          apply (simp_all)
       apply (erule (2) rel_funE)+
  done

definition rel_FGf_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself \<Rightarrow> bool" where
  "rel_FGf_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    (rel_FGf L1 L2 Co1 Co2 Contra1 Contra2 ::
      (_, _, _, _, _, _, 'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf \<Rightarrow> _) OO
      rel_FGf L1' L2' Co1' Co2' Contra1' Contra2' \<le>
    rel_FGf (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2'))"

definition rel_FGf_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself \<Rightarrow> bool" where
  "rel_FGf_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    rel_FGf (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2') \<le>
    (rel_FGf L1 L2 Co1 Co2 Contra1 Contra2 ::
      (_, _, _, _, _, _,'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf \<Rightarrow> _) OO
      rel_FGf L1' L2' Co1' Co2' Contra1' Contra2')"

text \<open>Sufficient conditions for subdistributivity over relation composition.\<close>

lemma rel_FGf_pos_distr_imp:
  fixes tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f2 \<times> 'f2 \<times> 'f2 \<times>
      ('f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) G) itself"
    and tytok_FGf :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself"
  assumes "rel_F_pos_distr_cond Co1 Co1' Co2 Co2' ((=) :: 'f4 \<Rightarrow> _) ((=) :: 'f4 \<Rightarrow> _)
      Contra1 Contra1' Contra2 Contra2' ((=) :: 'f6 \<Rightarrow> _) ((=) :: 'f6 \<Rightarrow> _) tytok_F"
  shows "rel_FGf_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_FGf"
  unfolding rel_FGf_pos_distr_cond_def rel_FGf_def
  apply (intro allI)
  apply (rule order_trans)
   apply (rule rel_F_pos_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (simp_all add: eq_OO)
  done

lemma rel_FGf_neg_distr_imp:
  fixes tytok_F :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f2 \<times> 'f2 \<times> 'f2 \<times>
      ('f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) G) itself"
    and tytok_FGf :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself"
  assumes "rel_F_neg_distr_cond Co1 Co1' Co2 Co2' ((=) :: 'f4 \<Rightarrow> _) ((=) :: 'f4 \<Rightarrow> _)
      Contra1 Contra1' Contra2 Contra2' ((=) :: 'f6 \<Rightarrow> _) ((=) :: 'f6 \<Rightarrow> _) tytok_F"
  shows "rel_FGf_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_FGf"
  unfolding rel_FGf_neg_distr_cond_def rel_FGf_def
  apply (intro allI)
  apply (rule order_trans[rotated])
   apply (rule rel_F_neg_distr)
   apply (rule assms(1))
  apply (rule rel_F_mono)
          apply (simp_all add: eq_OO)
  done

lemma rel_FGf_pos_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself"
  shows "rel_FGf_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  by (intro rel_FGf_pos_distr_imp rel_F_pos_distr_cond_eq)

lemma rel_FGf_neg_distr_cond_eq:
  fixes tytok :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times>
      'f1 \<times> 'f2 \<times> 'f3 \<times> 'f4 \<times> 'f5 \<times> 'f6 \<times> 'f7) itself"
  shows "rel_FGf_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  by (intro rel_FGf_neg_distr_imp rel_F_neg_distr_cond_eq)

definition "rell_FGf L1 L2 = rel_FGf L1 L2 (=) (=) (=) (=)"
definition "mapl_FGf l1 l2 = map_FGf l1 l2 id id id id"

type_synonym ('co1, 'co2, 'contra1, 'contra2, 'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGfbd =
  "('co1, 'co2, 'f4, 'contra1, 'contra2, 'f6, ('f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) G) Fbd"

definition set1_FGf :: "('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2,
    'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf \<Rightarrow> 'l1 set" where
  "set1_FGf x = set1_F x"

definition set2_FGf :: "('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2,
    'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf \<Rightarrow> 'l2 set" where
  "set2_FGf x = set2_F x"

definition bd_FGf :: "('co1, 'co2, 'contra1, 'contra2, 'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGfbd rel"
  where "bd_FGf = bd_F"

lemma set1_FGf_map: "set1_FGf \<circ> mapl_FGf l1 l2 = image l1 \<circ> set1_FGf"
  by (simp add: fun_eq_iff set1_FGf_def mapl_FGf_def map_FGf_def mapl_F_def[symmetric]
      set1_F_map[THEN fun_cong, simplified])

lemma bd_FGf_card_order: "card_order bd_FGf"
  unfolding bd_FGf_def using bd_F_card_order .

lemma bd_FGf_cinfinite: "cinfinite bd_FGf"
  unfolding bd_FGf_def using bd_F_cinfinite .

lemma
  fixes x :: "(_, _, 'co1, 'co2, 'contra1, 'contra2, 'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGf"
  shows set1_FGf_bound: "card_of (set1_FGf x) \<le>o (bd_FGf :: ('co1, 'co2, 'contra1, 'contra2,
      'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGfbd rel)"
    and set2_FGf_bound: "card_of (set2_FGf x) \<le>o (bd_FGf :: ('co1, 'co2, 'contra1, 'contra2,
      'f1, 'f2, 'f3, 'f4, 'f5, 'f6, 'f7) FGfbd rel)"
  unfolding set1_FGf_def set2_FGf_def bd_FGf_def by (rule set1_F_bound set2_F_bound)+

lemma mapl_FGf_cong:
  assumes "\<And>z. z \<in> set1_FGf x \<Longrightarrow> l1 z = l1' z" and "\<And>z. z \<in> set2_FGf x \<Longrightarrow> l2 z = l2' z"
  shows "mapl_FGf l1 l2 x = mapl_FGf l1' l2' x"
  unfolding mapl_FGf_def map_FGf_def mapl_F_def[symmetric]
  by (auto 0 3 intro: mapl_F_cong assms simp add: set1_FGf_def set2_FGf_def)

lemma rell_FGf_mono_strong:
  assumes "rell_FGf L1 L2 x y"
    and "\<And>a b. a \<in> set1_FGf x \<Longrightarrow> b \<in> set1_FGf y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b"
    and "\<And>a b. a \<in> set2_FGf x \<Longrightarrow> b \<in> set2_FGf y \<Longrightarrow> L2 a b \<Longrightarrow> L2' a b"
  shows "rell_FGf L1' L2' x y"
  using assms(1) unfolding rell_FGf_def rel_FGf_def rell_F_def[symmetric]
  by (auto 0 3 intro: rell_F_mono_strong assms(2-3) simp add: set1_FGf_def set2_FGf_def)

end
