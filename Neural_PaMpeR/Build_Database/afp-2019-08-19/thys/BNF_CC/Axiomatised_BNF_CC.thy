(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Axiomatisation\<close>

theory Axiomatised_BNF_CC imports
  Preliminaries
  "HOL-Library.Rewrite"
begin

unbundle cardinal_syntax

text \<open>
  This theory axiomatises two \BNFCC{}s, which will be used to demonstrate the closedness of \BNFCC{}s
  under various operations.
\<close>

subsection \<open>First abstract \BNFCC{}\<close>

subsubsection \<open>Axioms and basic definitions\<close>

typedecl ('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F

text \<open>@{type F} has each three live, co-, and contravariant parameters, and one fixed parameter.\<close>

consts
  rel_F :: "('l1 \<Rightarrow> 'l1' \<Rightarrow> bool) \<Rightarrow> ('l2 \<Rightarrow> 'l2' \<Rightarrow> bool) \<Rightarrow> ('l3 \<Rightarrow> 'l3' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow>
    ('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<Rightarrow>
    ('l1', 'l2', 'l3', 'co1', 'co2', 'co3', 'contra1', 'contra2', 'contra3', 'f) F \<Rightarrow> bool"
  map_F :: "('l1 \<Rightarrow> 'l1') \<Rightarrow> ('l2 \<Rightarrow> 'l2') \<Rightarrow> ('l3 \<Rightarrow> 'l3') \<Rightarrow>
    ('co1 \<Rightarrow> 'co1') \<Rightarrow> ('co2 \<Rightarrow> 'co2') \<Rightarrow> ('co3 \<Rightarrow> 'co3') \<Rightarrow>
    ('contra1' \<Rightarrow> 'contra1) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3) \<Rightarrow>
    ('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<Rightarrow>
    ('l1', 'l2', 'l3', 'co1', 'co2', 'co3', 'contra1', 'contra2', 'contra3', 'f) F"

axiomatization where
  rel_F_mono [mono]:
  "\<And>L1 L1' L2 L2' L3 L3' Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3'.
    \<lbrakk> L1 \<le> L1'; L2 \<le> L2'; L3 \<le> L3'; Co1 \<le> Co1'; Co2 \<le> Co2'; Co3 \<le> Co3';
      Contra1' \<le> Contra1; Contra2' \<le> Contra2; Contra3' \<le> Contra3 \<rbrakk> \<Longrightarrow>
    rel_F L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3 \<le>
    rel_F L1' L2' L3' Co1' Co2' Co3' Contra1' Contra2' Contra3'" and
  rel_F_eq: "rel_F (=) (=) (=) (=) (=) (=) (=) (=) (=) = (=)" and
  rel_F_conversep: "\<And>L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3.
    rel_F L1\<inverse>\<inverse> L2\<inverse>\<inverse> L3\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Co3\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> Contra3\<inverse>\<inverse> =
    (rel_F L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3)\<inverse>\<inverse>" and
  map_F_id0: "map_F id id id id id id id id id = id" and
  map_F_comp: "\<And>l1 l1' l2 l2' l3 l3' co1 co1' co2 co2' co3 co3'
    contra1 contra1' contra2 contra2' contra3 contra3'.
    map_F l1 l2 l3 co1 co2 co3 contra1 contra2 contra3 \<circ>
      map_F l1' l2' l3' co1' co2' co3' contra1' contra2' contra3' =
    map_F (l1 \<circ> l1') (l2 \<circ> l2') (l3 \<circ> l3') (co1 \<circ> co1') (co2 \<circ> co2') (co3 \<circ> co3')
      (contra1' \<circ> contra1) (contra2' \<circ> contra2) (contra3' \<circ> contra3)" and
  map_F_parametric:
  "\<And>L1 L1' L2 L2' L3 L3' Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3'.
    rel_fun (rel_fun L1 L1') (rel_fun (rel_fun L2 L2') (rel_fun (rel_fun L3 L3')
      (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2') (rel_fun (rel_fun Co3 Co3')
      (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
      (rel_fun (rel_fun Contra3' Contra3)
      (rel_fun (rel_F L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3)
      (rel_F L1' L2' L3' Co1' Co2' Co3' Contra1' Contra2' Contra3')))))))))) map_F map_F"

definition rel_F_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_F_pos_distr_cond Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool)
    (L3 :: 'l3 \<Rightarrow> 'l3' \<Rightarrow> bool) (L3' :: 'l3' \<Rightarrow> 'l3'' \<Rightarrow> bool).
    (rel_F L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3 ::
      (_, _, _, _, _, _, _, _, _, 'f) F \<Rightarrow> _) OO
      rel_F L1' L2' L3' Co1' Co2' Co3' Contra1' Contra2' Contra3' \<le>
    rel_F (L1 OO L1') (L2 OO L2') (L3 OO L3') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3'))"

definition rel_F_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'l3 \<times> 'l3' \<times> 'l3'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_F_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool)
    (L3 :: 'l3 \<Rightarrow> 'l3' \<Rightarrow> bool) (L3' :: 'l3' \<Rightarrow> 'l3'' \<Rightarrow> bool).
    rel_F (L1 OO L1') (L2 OO L2') (L3 OO L3') (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
      (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') \<le>
    (rel_F L1 L2 L3 Co1 Co2 Co3 Contra1 Contra2 Contra3 ::
      (_, _, _, _, _, _, _, _, _, 'f) F \<Rightarrow> _) OO
      rel_F L1' L2' L3' Co1' Co2' Co3' Contra1' Contra2' Contra3')"

axiomatization where
  rel_F_pos_distr_cond_eq:
  "\<And>tytok. rel_F_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  and
  rel_F_neg_distr_cond_eq:
  "\<And>tytok. rel_F_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) (=) tytok"

text \<open>Restrictions to live variables.\<close>

definition "rell_F L1 L2 L3 = rel_F L1 L2 L3 (=) (=) (=) (=) (=) (=)"
definition "mapl_F l1 l2 l3 = map_F l1 l2 l3 id id id id id id"

typedecl ('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd

consts
  set1_F :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<Rightarrow> 'l1 set"
  set2_F :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<Rightarrow> 'l2 set"
  set3_F :: "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<Rightarrow> 'l3 set"
  bd_F :: "('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd rel"

axiomatization where
  set1_F_map: "\<And>l1 l2 l3. set1_F \<circ> mapl_F l1 l2 l3 = image l1 \<circ> set1_F" and
  set2_F_map: "\<And>l1 l2 l3. set2_F \<circ> mapl_F l1 l2 l3 = image l2 \<circ> set2_F" and
  set3_F_map: "\<And>l1 l2 l3. set3_F \<circ> mapl_F l1 l2 l3 = image l3 \<circ> set3_F" and
  bd_F_card_order: "card_order bd_F" and
  bd_F_cinfinite: "cinfinite bd_F" and
  set1_F_bound: "\<And>x :: (_, _, _, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F.
    card_of (set1_F x) \<le>o (bd_F :: ('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd rel)" and
  set2_F_bound: "\<And>x :: (_, _, _, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F.
    card_of (set2_F x) \<le>o (bd_F :: ('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd rel)" and
  set3_F_bound: "\<And>x :: (_, _, _, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F.
    card_of (set3_F x) \<le>o (bd_F :: ('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd rel)" and
  mapl_F_cong: "\<And>l1 l1' l2 l2' l3 l3' x.
    \<lbrakk> \<And>z. z \<in> set1_F x \<Longrightarrow> l1 z = l1' z; \<And>z. z \<in> set2_F x \<Longrightarrow> l2 z = l2' z;
      \<And>z. z \<in> set3_F x \<Longrightarrow> l3 z = l3' z \<rbrakk> \<Longrightarrow>
    mapl_F l1 l2 l3 x = mapl_F l1' l2' l3' x" and
  rell_F_mono_strong: "\<And>L1 L1' L2 L2' L3 L3' x y.
    \<lbrakk> rell_F L1 L2 L3 x y;
      \<And>a b. a \<in> set1_F x \<Longrightarrow> b \<in> set1_F y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b;
      \<And>a b. a \<in> set2_F x \<Longrightarrow> b \<in> set2_F y \<Longrightarrow> L2 a b \<Longrightarrow> L2' a b;
      \<And>a b. a \<in> set3_F x \<Longrightarrow> b \<in> set3_F y \<Longrightarrow> L3 a b \<Longrightarrow> L3' a b \<rbrakk> \<Longrightarrow>
    rell_F L1' L2' L3' x y"


subsubsection \<open>Derived rules\<close>

lemmas rel_F_mono' = rel_F_mono[THEN predicate2D, rotated -1]

lemma rel_F_eq_refl: "rel_F (=) (=) (=) (=) (=) (=) (=) (=) (=) x x"
  by (simp add: rel_F_eq)

lemma map_F_id: "map_F id id id id id id id id id x = x"
  by (simp add: map_F_id0)

lemmas map_F_rel_cong = map_F_parametric[unfolded rel_fun_def, rule_format, rotated -1]

lemma rell_F_mono: "\<lbrakk> L1 \<le> L1'; L2 \<le> L2'; L3 \<le> L3' \<rbrakk> \<Longrightarrow> rell_F L1 L2 L3 \<le> rell_F L1' L2' L3'"
  unfolding rell_F_def by (rule rel_F_mono) (auto)

lemma mapl_F_id0: "mapl_F id id id = id"
  unfolding mapl_F_def using map_F_id0 .

lemma mapl_F_id: "mapl_F id id id x = x"
  by (simp add: mapl_F_id0)

lemma mapl_F_comp: "mapl_F l1 l2 l3 \<circ> mapl_F l1' l2' l3' = mapl_F (l1 \<circ> l1') (l2 \<circ> l2') (l3 \<circ> l3')"
  unfolding mapl_F_def
  apply (rule trans)
   apply (rule map_F_comp)
  apply (simp)
  done

lemma map_F_mapl_F: "map_F l1 l2 l3 co1 co2 co3 contra1 contra2 contra3 x =
  map_F id id id co1 co2 co3 contra1 contra2 contra3 (mapl_F l1 l2 l3 x)"
  unfolding mapl_F_def map_F_comp[THEN fun_cong, simplified] by simp

lemma mapl_F_map_F: "mapl_F l1 l2 l3 (map_F id id id co1 co2 co3 contra1 contra2 contra3 x) =
  map_F l1 l2 l3 co1 co2 co3 contra1 contra2 contra3 x"
  unfolding mapl_F_def map_F_comp[THEN fun_cong, simplified] by simp

text \<open>Parametric mappers are unique:\<close>

lemma rel_F_Grp_weak: "rel_F (Grp UNIV l1) (Grp UNIV l2) (Grp UNIV l3)
    (Grp UNIV co1) (Grp UNIV co2) (Grp UNIV co3)
    (Grp UNIV contra1)\<inverse>\<inverse> (Grp UNIV contra2)\<inverse>\<inverse> (Grp UNIV contra3)\<inverse>\<inverse> =
  Grp UNIV (map_F l1 l2 l3 co1 co2 co3 contra1 contra2 contra3)"
  apply (rule antisym)
   apply (rule predicate2I)
   apply (rule GrpI)
    apply (rewrite in "_ = \<hole>" map_F_id[symmetric])
    apply (subst rel_F_eq[symmetric])
    apply (erule map_F_rel_cong; simp add: Grp_def)
   apply (rule UNIV_I)
  apply (rule predicate2I)
  apply (erule GrpE)
  apply (drule sym)
  apply (hypsubst)
  apply (rewrite in "rel_F _ _ _ _ _ _ _ _ _ \<hole>" map_F_id[symmetric])
  apply (rule map_F_rel_cong)
           apply (rule rel_F_eq_refl)
          apply (simp_all add: Grp_def)
  done

lemmas
  rel_F_pos_distr = rel_F_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_F_neg_distr = rel_F_neg_distr_cond_def[THEN iffD1, rule_format]

lemma rell_F_compp:
  "rell_F (L1 OO L1') (L2 OO L2') (L3 OO L3') = rell_F L1 L2 L3 OO rell_F L1' L2' L3'"
  unfolding rell_F_def
  apply (rule antisym)
   apply (rule order_trans[rotated])
    apply (rule rel_F_neg_distr)
    apply (rule rel_F_neg_distr_cond_eq)
   apply (simp add: eq_OO)
  apply (rule order_trans)
   apply (rule rel_F_pos_distr)
   apply (rule rel_F_pos_distr_cond_eq)
  apply (simp add: eq_OO)
  done


subsubsection \<open>F is a BNF\<close>

lemma rell_F_eq_onp: "rell_F (eq_onp P1) (eq_onp P2) (eq_onp P3) =
  eq_onp (\<lambda>x. (\<forall>z\<in>set1_F x. P1 z) \<and> (\<forall>z\<in>set2_F x. P2 z) \<and> (\<forall>z\<in>set3_F x. P3 z))"
  (is "?rel_eq_onp = ?eq_onp_pred")
proof (intro ext iffI)
  fix x y
  assume rel: "?rel_eq_onp x y"
  from rel have "rell_F (=) (=) (=) x y"
    unfolding rell_F_def by (auto elim: rel_F_mono' simp add: eq_onp_def)
  then have "y = x" unfolding rell_F_def rel_F_eq ..
  let ?true = "\<lambda>_. True" and ?label = "\<lambda>P x. P x"
  from rel have "rell_F (=) (=) (=) (mapl_F ?true ?true ?true x)
    (mapl_F (?label P1) (?label P2) (?label P3) x)"
    unfolding rell_F_def mapl_F_def \<open>y = x\<close>
    by (auto simp add: eq_onp_def elim: map_F_rel_cong)
  then have *: "mapl_F ?true ?true ?true x = mapl_F (?label P1) (?label P2) (?label P3) x"
    unfolding rell_F_def rel_F_eq .
  note \<open>y = x\<close>
  moreover {
    from *
    have "set1_F (mapl_F ?true ?true ?true x) = set1_F (mapl_F (?label P1) (?label P2) (?label P3) x)"
      by simp
    then have "?true ` set1_F x = ?label P1 ` set1_F x"
      unfolding set1_F_map[THEN fun_cong, simplified] .
    then have "\<forall>z\<in>set1_F x. P1 z" by auto
  }
  moreover {
    from *
    have "set2_F (mapl_F ?true ?true ?true x) = set2_F (mapl_F (?label P1) (?label P2) (?label P3) x)"
      by simp
    then have "?true ` set2_F x = ?label P2 ` set2_F x"
      unfolding set2_F_map[THEN fun_cong, simplified] .
    then have "\<forall>z\<in>set2_F x. P2 z" by auto
  }
  moreover {
    from *
    have "set3_F (mapl_F ?true ?true ?true x) = set3_F (mapl_F (?label P1) (?label P2) (?label P3) x)"
      by simp
    then have "?true ` set3_F x = ?label P3 ` set3_F x"
      unfolding set3_F_map[THEN fun_cong, simplified] .
    then have "\<forall>z\<in>set3_F x. P3 z" by auto
  }
  ultimately show "?eq_onp_pred x y" by (simp add: eq_onp_def)
next
  fix x y
  assume eq_onp: "?eq_onp_pred x y"
  then have "rell_F (=) (=) (=) x y"
    by (auto simp add: rell_F_def rel_F_eq eq_onp_def)
  then show "?rel_eq_onp x y"
    using eq_onp by (auto elim!: rell_F_mono_strong simp add: eq_onp_def)
qed

lemma rell_F_Grp: "rell_F (Grp A1 f1) (Grp A2 f2) (Grp A3 f3) =
  Grp {x. set1_F x \<subseteq> A1 \<and> set2_F x \<subseteq> A2 \<and> set3_F x \<subseteq> A3} (mapl_F f1 f2 f3)"
proof -
  have "rell_F (Grp A1 f1) (Grp A2 f2) (Grp A3 f3) = rell_F (eq_onp (\<lambda>x. x \<in> A1) OO Grp UNIV f1)
    (eq_onp (\<lambda>x. x \<in> A2) OO Grp UNIV f2) (eq_onp (\<lambda>x. x \<in> A3) OO Grp UNIV f3)"
    by (simp add: eq_onp_compp_Grp)
  also have "... = rell_F (eq_onp (\<lambda>x. x \<in> A1)) (eq_onp (\<lambda>x. x \<in> A2)) (eq_onp (\<lambda>x. x \<in> A3)) OO
    rell_F (Grp UNIV f1) (Grp UNIV f2) (Grp UNIV f3)"
    using rell_F_compp .
  also have "... = eq_onp (\<lambda>x. set1_F x \<subseteq> A1 \<and> set2_F x \<subseteq> A2 \<and> set3_F x \<subseteq> A3) OO
    rell_F (Grp UNIV f1) (Grp UNIV f2) (Grp UNIV f3)"
    by (simp add: rell_F_eq_onp subset_eq)
  also have "... = eq_onp (\<lambda>x. set1_F x \<subseteq> A1 \<and> set2_F x \<subseteq> A2 \<and> set3_F x \<subseteq> A3) OO
    Grp UNIV (mapl_F f1 f2 f3)"
    unfolding rell_F_def mapl_F_def
      rel_F_Grp_weak[of _ _ _ id id id id id id, folded eq_alt, simplified]
    ..
  also have "... = Grp {x. set1_F x \<subseteq> A1 \<and> set2_F x \<subseteq> A2 \<and> set3_F x \<subseteq> A3} (mapl_F f1 f2 f3)"
    by (simp add: eq_onp_compp_Grp)
  finally show ?thesis .
qed

lemma rell_F_compp_Grp: "rell_F L1 L2 L3 =
  (Grp {x. set1_F x \<subseteq> {(x, y). L1 x y} \<and> set2_F x \<subseteq> {(x, y). L2 x y} \<and> set3_F x \<subseteq> {(x, y). L3 x y}}
    (mapl_F fst fst fst))\<inverse>\<inverse> OO
  Grp {x. set1_F x \<subseteq> {(x, y). L1 x y} \<and> set2_F x \<subseteq> {(x, y). L2 x y} \<and> set3_F x \<subseteq> {(x, y). L3 x y}}
    (mapl_F snd snd snd)"
  apply (unfold rell_F_Grp[symmetric])
  apply (unfold rell_F_def)
  apply (simp add: rel_F_conversep[symmetric])
  apply (fold rell_F_def)
  apply (simp add: rell_F_compp[symmetric] Grp_fst_snd)
  done

lemma F_in_rell: "rell_F L1 L2 L3 = (\<lambda>x y. \<exists>z. (set1_F z \<subseteq> {(x, y). L1 x y} \<and>
  set2_F z \<subseteq> {(x, y). L2 x y} \<and> set3_F z \<subseteq> {(x, y). L3 x y}) \<and>
  mapl_F fst fst fst z = x \<and> mapl_F snd snd snd z = y)"
  using rell_F_compp_Grp by (simp add: OO_Grp_alt)

bnf "('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F"
  map: mapl_F
  sets: set1_F set2_F set3_F
  bd: "bd_F :: ('co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) Fbd rel"
  rel: rell_F
  by (fact mapl_F_id0 mapl_F_comp[symmetric] mapl_F_cong set1_F_map set2_F_map set3_F_map
    bd_F_card_order bd_F_cinfinite set1_F_bound set2_F_bound set3_F_bound
    rell_F_compp[symmetric, THEN eq_refl] F_in_rell)+


subsubsection \<open>Composition witness\<close>

consts
  rel_F_witness :: "('l1 \<Rightarrow> 'l1'' \<Rightarrow> bool) \<Rightarrow> ('l2 \<Rightarrow> 'l2'' \<Rightarrow> bool) \<Rightarrow> ('l3 \<Rightarrow> 'l3'' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('co3 \<Rightarrow> 'co3' \<Rightarrow> bool) \<Rightarrow> ('co3' \<Rightarrow> 'co3'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra3 \<Rightarrow> 'contra3' \<Rightarrow> bool) \<Rightarrow> ('contra3' \<Rightarrow> 'contra3'' \<Rightarrow> bool) \<Rightarrow>
    ('l1, 'l2, 'l3, 'co1, 'co2, 'co3, 'contra1, 'contra2, 'contra3, 'f) F \<times>
    ('l1'', 'l2'', 'l3'', 'co1'', 'co2'', 'co3'', 'contra1'', 'contra2'', 'contra3'', 'f) F \<Rightarrow>
    ('l1 \<times> 'l1'', 'l2 \<times> 'l2'', 'l3 \<times> 'l3'', 'co1', 'co2', 'co3', 'contra1', 'contra2', 'contra3',
      'f) F"

specification (rel_F_witness)
  rel_F_witness1: "\<And>L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times>
      'l3 \<times> ('l3 \<times> 'l3'') \<times> 'l3'' \<times> 'f) itself)
    (x :: ('l1, 'l2, 'l3, _, _, _, _, _, _, 'f) F)
    (y :: ('l1'', 'l2'', 'l3'', _, _, _, _, _, _, 'f) F).
    \<lbrakk> rel_F_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3'
        Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' tytok;
      rel_F L1 L2 L3 (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
          (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') x y \<rbrakk> \<Longrightarrow>
    rel_F (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y)
    (\<lambda>x (x', y). x' = x \<and> L3 x y) Co1 Co2 Co3 Contra1 Contra2 Contra3 x
    (rel_F_witness L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3'
      Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' (x, y))"
  rel_F_witness2:"\<And>L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3'
    Contra1 Contra1' Contra2 Contra2' Contra3 Contra3'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times>
      'l3 \<times> ('l3 \<times> 'l3'') \<times> 'l3'' \<times> 'f) itself)
    (x :: ('l1, 'l2, 'l3, _, _, _, _, _, _, 'f) F)
    (y :: ('l1'', 'l2'', 'l3'', _, _, _, _, _, _, 'f) F).
    \<lbrakk> rel_F_neg_distr_cond Co1 Co1' Co2 Co2' Co3 Co3'
        Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' tytok;
      rel_F L1 L2 L3 (Co1 OO Co1') (Co2 OO Co2') (Co3 OO Co3')
          (Contra1 OO Contra1') (Contra2 OO Contra2') (Contra3 OO Contra3') x y \<rbrakk> \<Longrightarrow>
    rel_F (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y)
    (\<lambda>(x, y') y. y' = y \<and> L3 x y) Co1' Co2' Co3' Contra1' Contra2' Contra3'
    (rel_F_witness L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3'
       Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' (x, y)) y"
  apply(rule exI[where x="\<lambda>L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3'
     Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' (x, y). SOME z.
     rel_F (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) (\<lambda>x (x', y). x' = x \<and> L3 x y)
      Co1 Co2 Co3 Contra1 Contra2 Contra3 x z \<and>
     rel_F (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) (\<lambda>(x, y') y. y' = y \<and> L3 x y)
      Co1' Co2' Co3' Contra1' Contra2' Contra3' z y"])
  apply(fold all_conj_distrib)
  apply(rule allI)+
  apply(fold imp_conjR)
  apply(rule impI)+
  apply clarify
  apply(rule someI_ex)
  subgoal for L1 L2 L3 Co1 Co1' Co2 Co2' Co3 Co3' Contra1 Contra1' Contra2 Contra2' Contra3 Contra3' x y
    apply(drule rel_F_neg_distr[where
          ?L1.0 = "\<lambda>x (x', y). x' = x \<and> L1 x y" and ?L1'.0 = "\<lambda>(x, y) y'. y = y' \<and> L1 x y'" and
          ?L2.0 = "\<lambda>x (x', y). x' = x \<and> L2 x y" and ?L2'.0 = "\<lambda>(x, y) y'. y = y' \<and> L2 x y'" and
          ?L3.0 = "\<lambda>x (x', y). x' = x \<and> L3 x y" and ?L3'.0 = "\<lambda>(x, y) y'. y = y' \<and> L3 x y'"])
    apply(drule predicate2D)
     apply(erule rel_F_mono[THEN predicate2D, rotated -1]; fastforce)
    apply(erule relcomppE)
    apply(rule exI conjI)+
     apply assumption+
    done
  done


subsection \<open>Second abstract \BNFCC{}\<close>

subsubsection \<open>Axioms and basic definitions\<close>

typedecl ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G

text \<open>@{type G} has each two live, co, and contravariant parameters, and one fixed parameter.\<close>

consts
  rel_G :: "('l1 \<Rightarrow> 'l1' \<Rightarrow> bool) \<Rightarrow> ('l2 \<Rightarrow> 'l2' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow>
    ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G \<Rightarrow>
    ('l1', 'l2', 'co1', 'co2', 'contra1', 'contra2', 'f) G \<Rightarrow> bool"
  map_G :: "('l1 \<Rightarrow> 'l1') \<Rightarrow> ('l2 \<Rightarrow> 'l2') \<Rightarrow>
    ('co1 \<Rightarrow> 'co1') \<Rightarrow> ('co2 \<Rightarrow> 'co2') \<Rightarrow>
    ('contra1' \<Rightarrow> 'contra1) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2) \<Rightarrow>
    ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G \<Rightarrow>
    ('l1', 'l2', 'co1', 'co2', 'contra1', 'contra2', 'f) G"

axiomatization where
  rel_G_mono [mono]:
  "\<And>L1 L1' L2 L2' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'.
    \<lbrakk> L1 \<le> L1'; L2 \<le> L2'; Co1 \<le> Co1'; Co2 \<le> Co2'; Contra1' \<le> Contra1; Contra2' \<le> Contra2 \<rbrakk> \<Longrightarrow>
    rel_G L1 L2 Co1 Co2 Contra1 Contra2 \<le> rel_G L1' L2' Co1' Co2' Contra1' Contra2'" and
  rel_G_eq: "rel_G (=) (=) (=) (=) (=) (=) = (=)" and
  rel_G_conversep: "\<And>L1 L2 Co1 Co2 Contra1 Contra2.
    rel_G L1\<inverse>\<inverse> L2\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> = (rel_G L1 L2 Co1 Co2 Contra1 Contra2)\<inverse>\<inverse>" and
  map_G_id0: "map_G id id id id id id = id" and
  map_G_comp: "\<And>l1 l1' l2 l2' co1 co1' co2 co2' contra1 contra1' contra2 contra2'.
    map_G l1 l2 co1 co2 contra1 contra2 \<circ> map_G l1' l2' co1' co2' contra1' contra2' =
      map_G (l1 \<circ> l1') (l2 \<circ> l2') (co1 \<circ> co1') (co2 \<circ> co2')
      (contra1' \<circ> contra1) (contra2' \<circ> contra2)" and
  map_G_parametric:
  "\<And>L1 L1' L2 L2' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'.
    rel_fun (rel_fun L1 L1') (rel_fun (rel_fun L2 L2')
      (rel_fun (rel_fun Co1 Co1') (rel_fun (rel_fun Co2 Co2')
      (rel_fun (rel_fun Contra1' Contra1) (rel_fun (rel_fun Contra2' Contra2)
      (rel_fun (rel_G L1 L2 Co1 Co2 Contra1 Contra2)
      (rel_G L1' L2' Co1' Co2' Contra1' Contra2')))))))
      map_G map_G"

definition rel_G_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_G_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    (rel_G L1 L2 Co1 Co2 Contra1 Contra2 :: (_, _, _, _, _, _, 'f) G \<Rightarrow> _) OO
      rel_G L1' L2' Co1' Co2' Contra1' Contra2' \<le>
    rel_G (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2'))"

definition rel_G_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_G_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    rel_G (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2') \<le>
    (rel_G L1 L2 Co1 Co2 Contra1 Contra2 :: (_, _, _, _, _, _, 'f) G \<Rightarrow> _) OO
      rel_G L1' L2' Co1' Co2' Contra1' Contra2')"

axiomatization where
  rel_G_pos_distr_cond_eq:
  "\<And>tytok. rel_G_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok" and
  rel_G_neg_distr_cond_eq:
  "\<And>tytok. rel_G_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok"

text \<open>Restrictions to live variables.\<close>

definition "rell_G L1 L2 = rel_G L1 L2 (=) (=) (=) (=)"
definition "mapl_G l1 l2 = map_G l1 l2 id id id id"

typedecl ('co1, 'co2, 'contra1, 'contra2, 'f) Gbd

consts
  set1_G :: "('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G \<Rightarrow> 'l1 set"
  set2_G :: "('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G \<Rightarrow> 'l2 set"
  bd_G :: "('co1, 'co2, 'contra1, 'contra2, 'f) Gbd rel"
  wit_G :: "'l2 \<Rightarrow> ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G"
    \<comment> \<open>non-emptiness witness for least fixpoint\<close>

axiomatization where
  set1_G_map: "\<And>l1 l2. set1_G \<circ> mapl_G l1 l2 = image l1 \<circ> set1_G" and
  set2_G_map: "\<And>l1 l2. set2_G \<circ> mapl_G l1 l2 = image l2 \<circ> set2_G" and
  bd_G_card_order: "card_order bd_G" and
  bd_G_cinfinite: "cinfinite bd_G" and
  set1_G_bound: "\<And>x :: (_, _, 'co1, 'co2, 'contra1, 'contra2, 'f) G.
    card_of (set1_G x) \<le>o (bd_G :: ('co1, 'co2, 'contra1, 'contra2, 'f) Gbd rel)" and
  set2_G_bound: "\<And>x :: (_, _, 'co1, 'co2, 'contra1, 'contra2, 'f) G.
    card_of (set2_G x) \<le>o (bd_G :: ('co1, 'co2, 'contra1, 'contra2, 'f) Gbd rel)" and
  mapl_G_cong: "\<And>l1 l1' l2 l2' l3 l3' x.
    \<lbrakk> \<And>z. z \<in> set1_G x \<Longrightarrow> l1 z = l1' z; \<And>z. z \<in> set2_G x \<Longrightarrow> l2 z = l2' z \<rbrakk> \<Longrightarrow>
    mapl_G l1 l2 x = mapl_G l1' l2' x" and
  rell_G_mono_strong: "\<And>L1 L1' L2 L2' x y.
    \<lbrakk> rell_G L1 L2 x y;
      \<And>a b. a \<in> set1_G x \<Longrightarrow> b \<in> set1_G y \<Longrightarrow> L1 a b \<Longrightarrow> L1' a b;
      \<And>a b. a \<in> set2_G x \<Longrightarrow> b \<in> set2_G y \<Longrightarrow> L2 a b \<Longrightarrow> L2' a b \<rbrakk> \<Longrightarrow>
    rell_G L1' L2' x y" and
  wit_G_set1: "\<And>l2 x. x \<in> set1_G (wit_G l2) \<Longrightarrow> False" and
  wit_G_set2: "\<And>l2 x. x \<in> set2_G (wit_G l2) \<Longrightarrow> x = l2"


subsubsection \<open>Derived rules\<close>

lemmas rel_G_mono' = rel_G_mono[THEN predicate2D, rotated -1]

lemma rel_G_eq_refl: "rel_G (=) (=) (=) (=) (=) (=) x x"
  by (simp add: rel_G_eq)

lemma map_G_id: "map_G id id id id id id x = x"
  by (simp add: map_G_id0)

lemmas map_G_rel_cong = map_G_parametric[unfolded rel_fun_def, rule_format, rotated -1]

lemma rell_G_mono: "\<lbrakk> L1 \<le> L1'; L2 \<le> L2' \<rbrakk> \<Longrightarrow> rell_G L1 L2 \<le> rell_G L1' L2'"
  unfolding rell_G_def by (rule rel_G_mono) (auto)

lemma mapl_G_id0: "mapl_G id id = id"
  unfolding mapl_G_def using map_G_id0 .

lemma mapl_G_id: "mapl_G id id x = x"
  by (simp add: mapl_G_id0)

lemma mapl_G_comp: "mapl_G l1 l2 \<circ> mapl_G l1' l2' = mapl_G (l1 \<circ> l1') (l2 \<circ> l2')"
  unfolding mapl_G_def
  apply (rule trans)
   apply (rule map_G_comp)
  apply (simp)
  done

lemma map_G_mapl_G:
  "map_G l1 l2 co1 co2 contra1 contra2 x = map_G id id co1 co2 contra1 contra2 (mapl_G l1 l2 x)"
  unfolding mapl_G_def map_G_comp[THEN fun_cong, simplified] by simp

lemma mapl_G_map_G:
  "mapl_G l1 l2 (map_G id id co1 co2 contra1 contra2 x) = map_G l1 l2 co1 co2 contra1 contra2 x"
  unfolding mapl_G_def map_G_comp[THEN fun_cong, simplified] by simp

text \<open>Parametric mappers are unique:\<close>

lemma rel_G_Grp_weak: "rel_G (Grp UNIV l1) (Grp UNIV l2) (Grp UNIV co1) (Grp UNIV co2)
  (Grp UNIV contra1)\<inverse>\<inverse> (Grp UNIV contra2)\<inverse>\<inverse> = Grp UNIV (map_G l1 l2 co1 co2 contra1 contra2)"
  apply (rule antisym)
   apply (rule predicate2I)
   apply (rule GrpI)
    apply (rewrite in "_ = \<hole>" map_G_id[symmetric])
    apply (subst rel_G_eq[symmetric])
    apply (erule map_G_rel_cong; simp add: Grp_def)
   apply (rule UNIV_I)
  apply (rule predicate2I)
  apply (erule GrpE)
  apply (drule sym)
  apply (hypsubst)
  apply (rewrite in "rel_G _ _ _ _ _ _ \<hole>" map_G_id[symmetric])
  apply (rule map_G_rel_cong)
        apply (rule rel_G_eq_refl)
       apply (simp_all add: Grp_def)
  done

lemmas
  rel_G_pos_distr = rel_G_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_G_neg_distr = rel_G_neg_distr_cond_def[THEN iffD1, rule_format]

lemma rell_G_compp:
  "rell_G (L1 OO L1') (L2 OO L2') = rell_G L1 L2 OO rell_G L1' L2'"
  unfolding rell_G_def
  apply (rule antisym)
   apply (rule order_trans[rotated])
    apply (rule rel_G_neg_distr)
    apply (rule rel_G_neg_distr_cond_eq)
   apply (simp add: eq_OO)
  apply (rule order_trans)
   apply (rule rel_G_pos_distr)
   apply (rule rel_G_pos_distr_cond_eq)
  apply (simp add: eq_OO)
  done


subsubsection \<open>G is a BNF\<close>

lemma rell_G_eq_onp:
  "rell_G (eq_onp P1) (eq_onp P2) = eq_onp (\<lambda>x. (\<forall>z\<in>set1_G x. P1 z) \<and> (\<forall>z\<in>set2_G x. P2 z))"
  (is "?rel_eq_onp = ?eq_onp_pred")
proof (intro ext iffI)
  fix x y
  assume rel: "?rel_eq_onp x y"
  from rel have "rell_G (=) (=) x y"
    unfolding rell_G_def by (auto elim: rel_G_mono' simp add: eq_onp_def)
  then have "y = x" unfolding rell_G_def rel_G_eq ..
  let ?true = "\<lambda>_. True" and ?label = "\<lambda>P x. P x"
  from rel have "rell_G (=) (=) (mapl_G ?true ?true x) (mapl_G (?label P1) (?label P2) x)"
    unfolding rell_G_def mapl_G_def \<open>y = x\<close>
    by (auto simp add: eq_onp_def elim: map_G_rel_cong)
  then have *: "mapl_G ?true ?true x = mapl_G (?label P1) (?label P2) x"
    unfolding rell_G_def rel_G_eq .
  note \<open>y = x\<close>
  moreover {
    from *
    have "set1_G (mapl_G ?true ?true x) = set1_G (mapl_G (?label P1) (?label P2) x)"
      by simp
    then have "?true ` set1_G x = ?label P1 ` set1_G x"
      unfolding set1_G_map[THEN fun_cong, simplified] .
    then have "\<forall>z\<in>set1_G x. P1 z" by auto
  }
  moreover {
    from *
    have "set2_G (mapl_G ?true ?true x) = set2_G (mapl_G (?label P1) (?label P2) x)"
      by simp
    then have "?true ` set2_G x = ?label P2 ` set2_G x"
      unfolding set2_G_map[THEN fun_cong, simplified] .
    then have "\<forall>z\<in>set2_G x. P2 z" by auto
  }
  ultimately show "?eq_onp_pred x y" by (simp add: eq_onp_def)
next
  fix x y
  assume eq_onp: "?eq_onp_pred x y"
  then have "rell_G (=) (=) x y"
    by (auto simp add: rell_G_def rel_G_eq eq_onp_def)
  then show "?rel_eq_onp x y"
    using eq_onp by (auto elim!: rell_G_mono_strong simp add: eq_onp_def)
qed

lemma rell_G_Grp:
  "rell_G (Grp A1 f1) (Grp A2 f2) = Grp {x. set1_G x \<subseteq> A1 \<and> set2_G x \<subseteq> A2} (mapl_G f1 f2)"
proof -
  have "rell_G (Grp A1 f1) (Grp A2 f2) = rell_G (eq_onp (\<lambda>x. x \<in> A1) OO Grp UNIV f1)
    (eq_onp (\<lambda>x. x \<in> A2) OO Grp UNIV f2)"
    by (simp add: eq_onp_compp_Grp)
  also have "... = rell_G (eq_onp (\<lambda>x. x \<in> A1)) (eq_onp (\<lambda>x. x \<in> A2)) OO
    rell_G (Grp UNIV f1) (Grp UNIV f2)"
    using rell_G_compp .
  also have "... = eq_onp (\<lambda>x. set1_G x \<subseteq> A1 \<and> set2_G x \<subseteq> A2) OO
    rell_G (Grp UNIV f1) (Grp UNIV f2)"
    by (simp add: rell_G_eq_onp subset_eq)
  also have "... = eq_onp (\<lambda>x. set1_G x \<subseteq> A1 \<and> set2_G x \<subseteq> A2) OO Grp UNIV (mapl_G f1 f2)"
    unfolding rell_G_def mapl_G_def
      rel_G_Grp_weak[of _ _ id id id id, folded eq_alt, simplified]
    ..
  also have "... = Grp {x. set1_G x \<subseteq> A1 \<and> set2_G x \<subseteq> A2} (mapl_G f1 f2)"
    by (simp add: eq_onp_compp_Grp)
  finally show ?thesis .
qed

lemma rell_G_compp_Grp: "rell_G L1 L2 =
  (Grp {x. set1_G x \<subseteq> {(x, y). L1 x y} \<and> set2_G x \<subseteq> {(x, y). L2 x y}} (mapl_G fst fst))\<inverse>\<inverse> OO
  Grp {x. set1_G x \<subseteq> {(x, y). L1 x y} \<and> set2_G x \<subseteq> {(x, y). L2 x y}} (mapl_G snd snd)"
  apply (unfold rell_G_Grp[symmetric])
  apply (unfold rell_G_def)
  apply (simp add: rel_G_conversep[symmetric])
  apply (fold rell_G_def)
  apply (simp add: rell_G_compp[symmetric] Grp_fst_snd)
  done

lemma G_in_rell: "rell_G L1 L2 = (\<lambda>x y. \<exists>z. (set1_G z \<subseteq> {(x, y). L1 x y} \<and>
  set2_G z \<subseteq> {(x, y). L2 x y}) \<and> mapl_G fst fst z = x \<and> mapl_G snd snd z = y)"
  using rell_G_compp_Grp by (simp add: OO_Grp_alt)

bnf "('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G"
  map: mapl_G
  sets: set1_G set2_G
  bd: "bd_G :: ('co1, 'co2, 'contra1, 'contra2, 'f) Gbd rel"
  wits: wit_G
  rel: rell_G
  by (fact mapl_G_id0 mapl_G_comp[symmetric] mapl_G_cong set1_G_map set2_G_map
    bd_G_card_order bd_G_cinfinite set1_G_bound set2_G_bound rell_G_compp[symmetric, THEN eq_refl]
    G_in_rell wit_G_set1 wit_G_set2)+


subsubsection \<open>Composition witness\<close>

consts
  rel_G_witness :: "('l1 \<Rightarrow> 'l1'' \<Rightarrow> bool) \<Rightarrow> ('l2 \<Rightarrow> 'l2'' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) G \<times>
    ('l1'', 'l2'', 'co1'', 'co2'', 'contra1'', 'contra2'', 'f) G \<Rightarrow>
    ('l1 \<times> 'l1'', 'l2 \<times> 'l2'', 'co1', 'co2', 'contra1', 'contra2', 'f) G"

specification (rel_G_witness)
  rel_G_witness1: "\<And>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself)
    (x :: ('l1, 'l2, _, _, _, _, 'f) G) (y :: ('l1'', 'l2'', _, _, _, _, 'f) G).
    \<lbrakk> rel_G_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok;
      rel_G L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y \<rbrakk> \<Longrightarrow>
    rel_G (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x
    (rel_G_witness L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y))"
  rel_G_witness2:"\<And>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself)
    (x :: ('l1, 'l2, _, _, _, _, 'f) G) (y :: ('l1'', 'l2'', _, _, _, _, 'f) G).
    \<lbrakk> rel_G_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok;
      rel_G L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y \<rbrakk> \<Longrightarrow>
    rel_G (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2'
    (rel_G_witness L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y)) y"
  apply(rule exI[where x="\<lambda>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y). SOME z.
     rel_G (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x z \<and>
     rel_G (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2' z y"])
  apply(fold all_conj_distrib)
  apply(rule allI)+
  apply(fold imp_conjR)
  apply(rule impI)+
  apply clarify
  apply(rule someI_ex)
  subgoal for L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' x y
    apply(drule rel_G_neg_distr[where
          ?L1.0 = "\<lambda>x (x', y). x' = x \<and> L1 x y" and ?L1'.0 = "\<lambda>(x, y) y'. y = y' \<and> L1 x y'" and
          ?L2.0 = "\<lambda>x (x', y). x' = x \<and> L2 x y" and ?L2'.0 = "\<lambda>(x, y) y'. y = y' \<and> L2 x y'"])
    apply(drule predicate2D)
     apply(erule rel_G_mono[THEN predicate2D, rotated -1]; fastforce)
    apply(erule relcomppE)
    apply(rule exI conjI)+
     apply assumption+
    done
  done

end
