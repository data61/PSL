(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Subtypes\<close>

theory Subtypes imports
  Axiomatised_BNF_CC
  "HOL-Library.BNF_Axiomatization"
begin

subsection \<open>\BNFCC{} structure\<close>

consts P :: "('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) G \<Rightarrow> bool"

axiomatization where
  P_map: "\<And>x l1 l2 co1 co2 contra1 contra2. P x \<Longrightarrow> P (map_G l1 l2 co1 co2 contra1 contra2 x)"
  \<comment> \<open>@{term "{x. P x}"} is closed under the mapper of @{type G}\<close>
and
  ex_P: "\<exists>x. P x" \<comment> \<open>@{term "{x. P x}"} is non-empty\<close>

typedef (overloaded) ('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S =
  "{x :: ('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) G. P x}" by (simp add: ex_P)

text \<open>The subtype @{type S} is isomorphic to the set @{term "{x. P x}"}.\<close>

context includes lifting_syntax
begin

definition rel_S :: "('live1 \<Rightarrow> 'live1' \<Rightarrow> bool) \<Rightarrow> ('live2 \<Rightarrow> 'live2' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow>
    ('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S \<Rightarrow>
    ('live1', 'live2', 'co1', 'co2', 'contra1', 'contra2', 'fixed) S \<Rightarrow> bool"
  where
    "rel_S L1 L2 Co1 Co2 Contra1 Contra2 = vimage2p Rep_S Rep_S (rel_G L1 L2 Co1 Co2 Contra1 Contra2)"

definition map_S :: "('live1 \<Rightarrow> 'live1') \<Rightarrow> ('live2 \<Rightarrow> 'live2') \<Rightarrow>
    ('co1 \<Rightarrow> 'co1') \<Rightarrow> ('co2 \<Rightarrow> 'co2') \<Rightarrow>
    ('contra1' \<Rightarrow> 'contra1) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2) \<Rightarrow>
    ('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S \<Rightarrow>
    ('live1', 'live2', 'co1', 'co2', 'contra1', 'contra2', 'fixed) S"
  where
    "map_S = (id ---> id ---> id ---> id ---> id ---> id ---> Rep_S ---> Abs_S) map_G"

lemma rel_S_mono:
  "\<lbrakk> L1 \<le> L1'; L2 \<le> L2'; Co1 \<le> Co1'; Co2 \<le> Co2'; Contra1' \<le> Contra1; Contra2' \<le> Contra2 \<rbrakk>
  \<Longrightarrow> rel_S L1 L2 Co1 Co2 Contra1 Contra2 \<le> rel_S L1' L2' Co1' Co2' Contra1' Contra2'"
  unfolding rel_S_def
  apply(rule predicate2I)
  apply(simp add: vimage2p_def)
  by(erule rel_G_mono')

lemma rel_S_eq: "rel_S (=) (=) (=) (=) (=) (=) = (=)"
  unfolding rel_S_def by(clarsimp simp add: vimage2p_def fun_eq_iff rel_G_eq Rep_S_inject)

lemma rel_S_conversep:
  "rel_S L1\<inverse>\<inverse> L2\<inverse>\<inverse> Co1\<inverse>\<inverse> Co2\<inverse>\<inverse> Contra1\<inverse>\<inverse> Contra2\<inverse>\<inverse> = (rel_S L1 L2 Co1 Co2 Contra1 Contra2)\<inverse>\<inverse>"
  unfolding rel_S_def apply(simp add: vimage2p_def)
  apply(subst rel_G_conversep)
  apply(simp add: map_fun_def fun_eq_iff)
  done

lemma map_S_id0: "map_S id id id id id id = id"
  by(simp add: map_S_def fun_eq_iff map_G_id Rep_S_inverse)

lemma map_S_id: "map_S id id id id id id x = x"
  by (simp add: map_S_id0)

lemma map_S_comp:
  "map_S l1 l2 co1 co2 contra1 contra2 \<circ> map_S l1' l2' co1' co2' contra1' contra2' =
  map_S (l1 \<circ> l1') (l2 \<circ> l2') (co1 \<circ> co1') (co2 \<circ> co2') (contra1' \<circ> contra1) (contra2' \<circ> contra2)"
  apply (rule ext)
  apply (simp add: map_S_def)
  apply (subst Abs_S_inverse)
  subgoal for x using Rep_S[of x] by(simp add: P_map)
  apply (subst map_G_comp[THEN fun_cong, simplified])
  apply simp
  done

lemma map_S_parametric:
  "((L1 ===> L1') ===> (L2 ===> L2') ===> (Co1 ===> Co1') ===> (Co2 ===> Co2') ===>
    (Contra1' ===> Contra1) ===> (Contra2' ===> Contra2) ===>
  rel_S L1 L2 Co1 Co2 Contra1 Contra2 ===> rel_S L1' L2' Co1' Co2' Contra1' Contra2')
  map_S map_S"
  apply(rule rel_funI)+
  unfolding rel_S_def map_S_def
  apply(simp add: vimage2p_def)
  apply(subst Abs_S_inverse)
  subgoal for \<dots> x _ using Rep_S[of x] by(simp add: P_map)
  apply(subst Abs_S_inverse)
  subgoal for \<dots> y using Rep_S[of y] by(simp add: P_map)
  by(erule map_G_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD,
        THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1])

lemmas map_S_rel_cong = map_S_parametric[unfolded rel_fun_def, rule_format, rotated -1]

end (* context includes lifting_syntax *)

definition rel_S_pos_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_S_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    (rel_S L1 L2 Co1 Co2 Contra1 Contra2 :: (_, _, _, _, _, _, 'f) S \<Rightarrow> _) OO
      rel_S L1' L2' Co1' Co2' Contra1' Contra2' \<le>
    rel_S (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2'))"

definition rel_S_neg_distr_cond :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself \<Rightarrow> bool" where
  "rel_S_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' _ \<longleftrightarrow>
  (\<forall>(L1 :: 'l1 \<Rightarrow> 'l1' \<Rightarrow> bool) (L1' :: 'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool)
    (L2 :: 'l2 \<Rightarrow> 'l2' \<Rightarrow> bool) (L2' :: 'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool).
    rel_S (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
      (Contra1 OO Contra1') (Contra2 OO Contra2') \<le>
    (rel_S L1 L2 Co1 Co2 Contra1 Contra2 :: (_, _, _, _, _, _, 'f) S \<Rightarrow> _) OO
      rel_S L1' L2' Co1' Co2' Contra1' Contra2')"

axiomatization where
  rel_S_neg_distr_cond_eq:
  "\<And>tytok. rel_S_neg_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok"


text \<open>The subtype inherits the conditions for positive subdistributivity.\<close>

lemma rel_S_pos_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_G :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself"
    and tytok_S :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself"
  assumes "rel_G_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_G"
  shows "rel_S_pos_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_S"
  unfolding rel_S_pos_distr_cond_def rel_S_def
  apply(simp add: vimage2p_def)
  apply(intro allI predicate2I)
  apply(clarsimp)
  apply(rule rel_G_pos_distr[THEN predicate2D])
   apply(rule assms)
  apply(rule relcomppI)
   apply simp
  apply simp
  done

lemma rel_S_pos_distr_cond_eq:
  "\<And>tytok. rel_S_pos_distr_cond (=) (=) (=) (=) (=) (=) (=) (=) tytok"
  by (intro rel_S_pos_distr_imp rel_G_pos_distr_cond_eq)

lemmas
  rel_S_pos_distr = rel_S_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_S_neg_distr = rel_S_neg_distr_cond_def[THEN iffD1, rule_format]

text \<open>
  The following composition witness depends only on the abstract condition
  @{const rel_S_neg_distr_cond}, without additional assumptions.
\<close>

consts
  rel_S_witness :: "('l1 \<Rightarrow> 'l1'' \<Rightarrow> bool) \<Rightarrow> ('l2 \<Rightarrow> 'l2'' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1, 'l2, 'co1, 'co2, 'contra1, 'contra2, 'f) S \<times>
    ('l1'', 'l2'', 'co1'', 'co2'', 'contra1'', 'contra2'', 'f) S \<Rightarrow>
    ('l1 \<times> 'l1'', 'l2 \<times> 'l2'', 'co1', 'co2', 'contra1', 'contra2', 'f) S"

specification (rel_S_witness)
  rel_S_witness1: "\<And>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself)
    (x :: ('l1, 'l2, _, _, _, _, 'f) S) (y :: ('l1'', 'l2'', _, _, _, _, 'f) S).
    \<lbrakk> rel_S_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok;
      rel_S L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y \<rbrakk> \<Longrightarrow>
    rel_S (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x
    (rel_S_witness L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y))"
  rel_S_witness2:"\<And>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself)
    (x :: ('l1, 'l2, _, _, _, _, 'f) S) (y :: ('l1'', 'l2'', _, _, _, _, 'f) S).
    \<lbrakk> rel_S_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok;
      rel_S L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y \<rbrakk> \<Longrightarrow>
    rel_S (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2'
    (rel_S_witness L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y)) y"
  apply(rule exI[where x="\<lambda>L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y). SOME z.
     rel_S (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x z \<and>
     rel_S (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2' z y"])
  apply(fold all_conj_distrib)
  apply(rule allI)+
  apply(fold imp_conjR)
  apply(rule impI)+
  apply clarify
  apply(rule someI_ex)
  subgoal for L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' x y
    apply(drule rel_S_neg_distr[where
          ?L1.0 = "\<lambda>x (x', y). x' = x \<and> L1 x y" and ?L1'.0 = "\<lambda>(x, y) y'. y = y' \<and> L1 x y'" and
          ?L2.0 = "\<lambda>x (x', y). x' = x \<and> L2 x y" and ?L2'.0 = "\<lambda>(x, y) y'. y = y' \<and> L2 x y'"])
    apply(drule predicate2D)
     apply(erule rel_S_mono[THEN predicate2D, rotated -1]; fastforce)
    apply(erule relcomppE)
    apply(rule exI conjI)+
     apply assumption+
    done
  done

definition set1_S :: "('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S \<Rightarrow> 'live1 set"
  where "set1_S = set1_G \<circ> Rep_S"

definition set2_S :: "('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S \<Rightarrow> 'live2 set"
  where "set2_S = set2_G \<circ> Rep_S"

lemma rel_S_alt:
  "rel_S L1 L2 (=) (=) (=) (=) x y \<longleftrightarrow> (\<exists>z. (set1_S z \<subseteq> {(x, y). L1 x y} \<and>
  set2_S z \<subseteq> {(x, y). L2 x y}) \<and> map_S fst fst id id id id z = x \<and> map_S snd snd id id id id z = y)"
  unfolding set1_S_def set2_S_def o_def
  apply(rule iffI)
  subgoal
    apply(subst (asm) (3 4 5 7) OO_eq[symmetric])
    apply(rule exI[where x="rel_S_witness L1 L2 (=) (=) (=) (=) (=) (=) (=) (=) (x, y)"])
    apply(frule rel_S_witness1[OF rel_S_neg_distr_cond_eq])
    apply(drule rel_S_witness2[OF rel_S_neg_distr_cond_eq])
    apply(auto simp add: rel_S_def vimage2p_def rell_G_def[symmetric])
       apply(drule (1) G.Domainp_rel[THEN eq_refl, THEN predicate1D,
          OF DomainPI, unfolded pred_G_def, THEN conjunct1, THEN bspec,
          of "conversep _" "conversep _",
          unfolded G.rel_conversep Domainp_conversep, unfolded conversep_iff])
       apply(simp add: Rangep.simps)
      apply(drule (1) G.Domainp_rel[THEN eq_refl, THEN predicate1D, OF DomainPI,
          unfolded pred_G_def, THEN conjunct2, THEN bspec, of "conversep _" "conversep _",
          unfolded G.rel_conversep Domainp_conversep, unfolded conversep_iff])
      apply(simp add: Rangep.simps)
     apply(rewrite in "_ = \<hole>" map_S_id[symmetric])
     apply(rule sym)
     apply(subst rel_S_eq[symmetric])
     apply(rule map_S_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD,
          THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1])
           apply(simp add: rel_S_def vimage2p_def)
           apply(subst rell_G_def[symmetric])
           apply assumption
          apply(simp_all add: rel_fun_def)
    apply(rewrite in "_ = \<hole>" map_S_id[symmetric])
    apply(subst rel_S_eq[symmetric])
    apply(rule map_S_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD,
          THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1])
          apply(simp add: rel_S_def vimage2p_def)
          apply(subst rell_G_def[symmetric])
          apply assumption
         apply(simp_all add: rel_fun_def)
    done
  subgoal
    apply(elim conjE exE)
    apply hypsubst
    apply(rule map_S_parametric[where ?L1.0="eq_onp (\<lambda>(x, y). L1 x y)" and
          ?L2.0="eq_onp (\<lambda>(x, y). L2 x y)", THEN rel_funD, THEN rel_funD, THEN rel_funD,
          THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1])
          apply(simp add: rel_S_def vimage2p_def)
          apply(subst rell_G_def[symmetric])
          apply(rule G.rel_refl_strong)
           apply(drule (1) subsetD)
           apply(simp add: eq_onp_def)
          apply(drule (1) subsetD)
          apply(simp add: eq_onp_def)
         apply(simp_all add: rel_fun_def eq_onp_def)
    done
  done

bnf "('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S"
  map: "\<lambda>l1 l2. map_S l1 l2 id id id id"
  sets: "set1_S" "set2_S"
  bd: "bd_G :: ('co1, 'co2, 'contra1, 'contra2, 'fixed) Gbd rel"
  rel: "\<lambda>L1 L2. rel_S L1 L2 (=) (=) (=) (=)"
  subgoal by (rule map_S_id0)
  subgoal by (simp add: map_S_comp)
  subgoal
    apply(simp add: map_S_def set1_S_def set2_S_def)
    apply(rule arg_cong[where f="Abs_S"])
    apply(fold mapl_G_def)
    apply(rule G.map_cong[OF refl])
     apply simp_all
    done
  subgoal
    apply(simp add: set1_S_def map_S_def fun_eq_iff)
    apply(subst Abs_S_inverse)
    subgoal for x using Rep_S[of x] by(simp add: P_map)
    apply(simp add: G.set_map mapl_G_def[symmetric])
    done
  subgoal
    apply(simp add: set2_S_def map_S_def fun_eq_iff)
    apply(subst Abs_S_inverse)
    subgoal for x using Rep_S[of x] by(simp add: P_map)
    apply(simp add: G.set_map mapl_G_def[symmetric])
    done
  subgoal by(rule bd_G_card_order)
  subgoal by(rule bd_G_cinfinite)
  subgoal
    apply (simp add: set1_S_def)
    apply (rule set1_G_bound)
    done
  subgoal
    apply (simp add: set2_S_def)
    apply (rule set2_G_bound)
    done
  subgoal
    apply(subst (23 24 25 27) eq_OO[symmetric])
    apply(rule rel_S_pos_distr_cond_def[THEN iffD1, rule_format])
    apply(rule rel_S_pos_distr_imp)
    apply(rule rel_G_pos_distr_cond_eq)
    done
  subgoal
    apply(rule ext)+
    apply(rule rel_S_alt)
    done
  done


subsection \<open>Closedness under zippings\<close>

lemma P_zip_closed: \<comment> \<open>This is @{command lift_bnf}'s property that is too strong.\<close>
  assumes "P (mapl_G fst fst z)" "P (mapl_G snd snd z)"
  shows "P z"
  oops

consts rel_S_neg_distr_cond' :: "('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself \<Rightarrow> bool"

text \<open>
  If the set @{term "{x. P x}"} is closed under zippings for @{const rel_S_neg_distr_cond'},
  we inherit the condition for negative subdistributivity from @{type G}.
\<close>

axiomatization where
  P_rel_G_zipping: "\<And>(L1 :: 'l1 \<Rightarrow> 'l1'' \<Rightarrow> bool) (L2 :: 'l2 \<Rightarrow> 'l2'' \<Rightarrow> bool)
    Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2'
    (tytok :: ('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself) x y z.
    \<lbrakk> P x; P y;
      rel_G L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y;
      rel_G (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x z;
      rel_G (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2' z y;
      rel_S_neg_distr_cond' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok \<rbrakk>
    \<Longrightarrow> P z"
  and
  rel_S_neg_distr_cond'_stronger: "\<And>Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok.
    rel_S_neg_distr_cond' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok \<Longrightarrow>
    rel_G_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok"
  and
  rel_S_neg_distr_cond'_eq:
  "\<And>tytok. rel_S_neg_distr_cond' (=) (=) (=) (=) (=) (=) (=) (=) tytok"

context includes lifting_syntax
begin

definition rel_S_witness' :: "('live1 \<Rightarrow> 'live1'' \<Rightarrow> bool) \<Rightarrow> ('live2 \<Rightarrow> 'live2'' \<Rightarrow> bool) \<Rightarrow>
    ('co1 \<Rightarrow> 'co1' \<Rightarrow> bool) \<Rightarrow> ('co1' \<Rightarrow> 'co1'' \<Rightarrow> bool) \<Rightarrow>
    ('co2 \<Rightarrow> 'co2' \<Rightarrow> bool) \<Rightarrow> ('co2' \<Rightarrow> 'co2'' \<Rightarrow> bool) \<Rightarrow>
    ('contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool) \<Rightarrow> ('contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool) \<Rightarrow>
    ('contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool) \<Rightarrow> ('contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool) \<Rightarrow>
    ('live1, 'live2, 'co1, 'co2, 'contra1, 'contra2, 'fixed) S \<times>
    ('live1'', 'live2'', 'co1'', 'co2'', 'contra1'', 'contra2'', 'fixed) S \<Rightarrow>
    ('live1 \<times> 'live1'', 'live2 \<times> 'live2'', 'co1', 'co2', 'contra1', 'contra2', 'fixed) S"
  where
    "rel_S_witness' = (id ---> id ---> id ---> id ---> id ---> id --->
    id ---> id ---> id ---> id ---> map_prod Rep_S Rep_S ---> Abs_S) rel_G_witness"

lemma rel_S_witness'1:
  fixes L1 :: "'l1 \<Rightarrow> 'l1'' \<Rightarrow> bool" and L2 :: "'l2 \<Rightarrow> 'l2'' \<Rightarrow> bool"
    and Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok :: "('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself"
    and x :: "(_, _, _, _, _, _, 'f) S"
  assumes "rel_S L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y"
    and "rel_S_neg_distr_cond' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok"
  shows "rel_S (\<lambda>x (x', y). x' = x \<and> L1 x y) (\<lambda>x (x', y). x' = x \<and> L2 x y) Co1 Co2 Contra1 Contra2 x
    (rel_S_witness' L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y))"
  using assms unfolding rel_S_def rel_S_witness'_def
  apply(simp add: vimage2p_def)
  apply(subst Abs_S_inverse)
   apply(simp)
   apply(rule P_rel_G_zipping[OF Rep_S[of x, simplified] Rep_S[of y, simplified], rotated])
      apply(erule rel_G_witness1[rotated])
      apply(erule rel_S_neg_distr_cond'_stronger)
     apply(erule rel_G_witness2[rotated])
     apply(erule rel_S_neg_distr_cond'_stronger)
    apply(assumption)
   apply(assumption)
  apply(erule rel_G_witness1[rotated])
  apply(erule rel_S_neg_distr_cond'_stronger)
  done

lemma rel_S_witness'2:
  fixes L1 :: "'l1 \<Rightarrow> 'l1'' \<Rightarrow> bool" and L2 :: "'l2 \<Rightarrow> 'l2'' \<Rightarrow> bool"
    and Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok :: "('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself"
    and x :: "(_, _, _, _, _, _, 'f) S"
  assumes "rel_S L1 L2 (Co1 OO Co1') (Co2 OO Co2') (Contra1 OO Contra1') (Contra2 OO Contra2') x y"
    and "rel_S_neg_distr_cond' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok"
  shows "rel_S (\<lambda>(x, y') y. y' = y \<and> L1 x y) (\<lambda>(x, y') y. y' = y \<and> L2 x y) Co1' Co2' Contra1' Contra2'
    (rel_S_witness' L1 L2 Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' (x, y)) y"
  using assms unfolding rel_S_def rel_S_witness'_def
  apply(simp add: vimage2p_def)
  apply(subst Abs_S_inverse)
   apply(simp)
   apply(rule P_rel_G_zipping[OF Rep_S[of x, simplified] Rep_S[of y, simplified], rotated])
      apply(erule rel_G_witness1[rotated])
      apply(erule rel_S_neg_distr_cond'_stronger)
     apply(erule rel_G_witness2[rotated])
     apply(erule rel_S_neg_distr_cond'_stronger)
    apply(assumption)
   apply(assumption)
  apply(erule rel_G_witness2[rotated])
  apply(erule rel_S_neg_distr_cond'_stronger)
  done

lemma rel_S_neg_distr_imp:
  fixes Co1 :: "'co1 \<Rightarrow> 'co1' \<Rightarrow> bool" and Co1' :: "'co1' \<Rightarrow> 'co1'' \<Rightarrow> bool"
    and Co2 :: "'co2 \<Rightarrow> 'co2' \<Rightarrow> bool" and Co2' :: "'co2' \<Rightarrow> 'co2'' \<Rightarrow> bool"
    and Contra1 :: "'contra1 \<Rightarrow> 'contra1' \<Rightarrow> bool" and Contra1' :: "'contra1' \<Rightarrow> 'contra1'' \<Rightarrow> bool"
    and Contra2 :: "'contra2 \<Rightarrow> 'contra2' \<Rightarrow> bool" and Contra2' :: "'contra2' \<Rightarrow> 'contra2'' \<Rightarrow> bool"
    and tytok_S' :: "('l1 \<times> ('l1 \<times> 'l1'') \<times> 'l1'' \<times> 'l2 \<times> ('l2 \<times> 'l2'') \<times> 'l2'' \<times> 'f) itself"
    and tytok_S :: "('l1 \<times> 'l1' \<times> 'l1'' \<times> 'l2 \<times> 'l2' \<times> 'l2'' \<times> 'f) itself"
  assumes "rel_S_neg_distr_cond' Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_S'"
  shows "rel_S_neg_distr_cond Co1 Co1' Co2 Co2' Contra1 Contra1' Contra2 Contra2' tytok_S"
  unfolding rel_S_neg_distr_cond_def
proof (intro allI predicate2I relcomppI)
  fix L1 :: "'l1 \<Rightarrow> 'l1' \<Rightarrow> bool" and L1' :: "'l1' \<Rightarrow> 'l1'' \<Rightarrow> bool"
    and L2 :: "'l2 \<Rightarrow> 'l2' \<Rightarrow> bool" and L2' :: "'l2' \<Rightarrow> 'l2'' \<Rightarrow> bool"
    and x :: "(_, _, _, _, _, _, 'f) S" and y :: "(_, _, _, _, _, _, 'f) S"
  assume *: "rel_S (L1 OO L1') (L2 OO L2') (Co1 OO Co1') (Co2 OO Co2')
    (Contra1 OO Contra1') (Contra2 OO Contra2') x y"
  let ?z = "map_S (relcompp_witness L1 L1') (relcompp_witness L2 L2') id id id id
    (rel_S_witness' (L1 OO L1') (L2 OO L2') Co1 Co1' Co2 Co2'
    Contra1 Contra1' Contra2 Contra2' (x, y))"
  show "rel_S L1 L2 Co1 Co2 Contra1 Contra2 x ?z"
    apply(subst map_S_id[symmetric])
    apply(rule map_S_rel_cong)
          apply(rule rel_S_witness'1[OF * assms])
         apply(auto simp add: vimage2p_def del: relcomppE elim!: relcompp_witness)
    done
  show "rel_S L1' L2' Co1' Co2' Contra1' Contra2' ?z y"
    apply(rewrite in "rel_S _ _ _ _ _ _ _ \<hole>" map_S_id[symmetric])
    apply(rule map_S_rel_cong)
          apply(rule rel_S_witness'2[OF * assms])
         apply(auto simp add: vimage2p_def del: relcomppE elim!: relcompp_witness)
    done
qed

end (* context includes lifting_syntax *)


subsection \<open>Subtypes of BNFs without co- and contravariance\<close>

text \<open>
  If all variables are live, @{command lift_bnf}'s requirement \<open>P_zip_closed\<close> is equivalent
  to our closedness under zippings, and Popescu's weaker condition is equivalent to negative
  subdistributivity restricted to the subset.
\<close>

bnf_axiomatization 'a H

consts Q :: "'a H \<Rightarrow> bool"

axiomatization where
  Q_map: "\<And>x l. Q x \<Longrightarrow> Q (map_H l x)"

lemma Q_rel_H_zipping:
  fixes x :: "'a H" and y :: "'c H" and z :: "('a \<times> 'c) H"
  assumes Q_zip: "\<And>z :: ('a \<times> 'c) H. \<lbrakk> Q (map_H fst z); Q (map_H snd z) \<rbrakk> \<Longrightarrow> Q z"
    and "Q x" and "Q y" and "rel_H L x y"
    and related: "rel_H (\<lambda>x (x', y). x' = x \<and> L x y) x z" "rel_H (\<lambda>(x, y') y. y' = y \<and> L x y) z y"
  shows "Q z"
proof -
  have "map_H fst z = x" proof -
    from related(1) have "rel_H (=) x (map_H fst z)"
      by (auto simp add: H.rel_map elim: H.rel_mono_strong)
    then show ?thesis by (simp add: H.rel_eq)
  qed
  moreover have "map_H snd z = y" proof -
    from related(2) have "rel_H (=) (map_H snd z) y"
      by (auto simp add: H.rel_map elim: H.rel_mono_strong)
    then show ?thesis by (simp add: H.rel_eq)
  qed
  moreover note \<open>Q x\<close> \<open>Q y\<close>
  ultimately show ?thesis using Q_zip by blast
qed

lemma Q_zip:
  fixes z :: "('a \<times> 'c) H"
  assumes Q_rel_H_zipping: "\<And>(L :: 'a \<Rightarrow> 'c \<Rightarrow> _) x y z.
      \<lbrakk> Q x; Q y; rel_H L x y; rel_H (\<lambda>x (x', y). x' = x \<and> L x y) x z;
        rel_H (\<lambda>(x, y') y. y' = y \<and> L x y) z y \<rbrakk> \<Longrightarrow> Q z"
    and "Q (map_H fst z)" and "Q (map_H snd z)"
  shows "Q z"
proof -
  let ?L = "\<lambda>a (a', b). a' = a \<and> top a b" and ?L' = "\<lambda>(b, c') c. c' = c \<and> top b c"
  have *: "rel_H ?L (map_H fst z) z" "rel_H ?L' z (map_H snd z)"
    by (auto simp add: H.rel_map Grp_apply intro!: H.rel_refl_strong)
  then have "rel_H (?L OO ?L') (map_H fst z) (map_H snd z)"
    by (auto simp add: H.rel_compp)
  then have "rel_H top (map_H fst z) (map_H snd z)"
    by (simp add: relcompp_apply[abs_def] top_fun_def)
  with \<open>Q (map_H fst z)\<close> \<open>Q (map_H snd z)\<close> * show "Q z"
    using Q_rel_H_zipping by blast
qed

lemma Q_neg_distr:
  fixes x :: "'a H" and y :: "'c H"
  assumes Q_zip_weak: "\<And>z :: ('a \<times> 'c) H. \<lbrakk> Q (map_H fst z); Q (map_H snd z) \<rbrakk> \<Longrightarrow>
      \<exists>z'. Q z' \<and> set_H z' \<subseteq> set_H z \<and> map_H fst z' = map_H fst z \<and> map_H snd z' = map_H snd z"
    and "Q x" and "Q y" and related: "rel_H (L OO L') x y"
  shows "(rel_H L OO eq_onp Q OO rel_H L') x y"
proof -
  from related obtain z where
    *: "set_H z \<subseteq> {(x, y). (L OO L') x y}" "map_H fst z = x" "map_H snd z = y"
    unfolding H.rel_compp_Grp by (blast elim: GrpE)
  with \<open>Q x\<close> \<open>Q y\<close> have "Q (map_H fst z)" and "Q (map_H snd z)" by simp_all
  then obtain z' where "Q z'" "set_H z' \<subseteq> set_H z"
    "map_H fst z' = map_H fst z" "map_H snd z' = map_H snd z"
    using Q_zip_weak by blast
  with * have **: "set_H z' \<subseteq> {(x, y). (L OO L') x y}" "x = map_H fst z'" "y = map_H snd z'"
    by simp_all
  let ?z = "map_H (relcompp_witness L L') z'"
  from \<open>Q z'\<close> have "Q ?z" by (rule Q_map)
  moreover have "rel_H L x ?z" "rel_H L' ?z y"
    using ** by (auto simp add: H.rel_map intro!: H.rel_refl_strong
        relcompp_witness[of L L' "fst p" "snd p" for p, simplified])
  ultimately show ?thesis unfolding eq_onp_def by blast
qed

lemma Q_zip_weak:
  fixes z :: "('a \<times> 'c) H"
  assumes Q_neg_distr: "\<And>(L :: 'a \<Rightarrow> ('a \<times> 'c) \<Rightarrow> _) (L' :: ('a \<times> 'c) \<Rightarrow> 'c \<Rightarrow> bool) x y.
      \<lbrakk> Q x; Q y; rel_H (L OO L') x y \<rbrakk> \<Longrightarrow> (rel_H L OO eq_onp Q OO rel_H L') x y"
    and "Q (map_H fst z)" and "Q (map_H snd z)"
  obtains z' where "Q z'" and "set_H z' \<subseteq> set_H z"
    and "map_H fst z' = map_H fst z" and "map_H snd z' = map_H snd z"
proof -
  let ?L = "(Grp (set_H z) fst)\<inverse>\<inverse>" and ?L' = "Grp (set_H z) snd"
  have "rel_H ?L (map_H fst z) z" "rel_H ?L' z (map_H snd z)"
    by (auto simp add: H.rel_map Grp_apply intro!: H.rel_refl_strong)
  then have "rel_H (?L OO ?L') (map_H fst z) (map_H snd z)"
    by (auto simp add: H.rel_compp)
  with \<open>Q (map_H fst z)\<close> \<open>Q (map_H snd z)\<close>
  have "(rel_H ?L OO eq_onp Q OO rel_H ?L') (map_H fst z) (map_H snd z)"
    by (rule Q_neg_distr)
  then obtain z' where "Q z'" "rel_H ?L (map_H fst z) z'" "rel_H ?L' z' (map_H snd z)"
    unfolding eq_onp_def by blast
  then have "rel_H (\<lambda>a b. snd b = snd a \<and> a \<in> set_H z) z' z"
    by (simp add: H.rel_map Grp_apply)
  then have "rel_H (\<lambda>a b. a \<in> set_H z) z' z"
    by (auto elim: H.rel_mono_strong)
  then have "pred_H (Domainp (\<lambda>a (b :: ('a \<times> 'c)). a \<in> set_H z)) z'"
    by (auto simp add: H.Domainp_rel[symmetric] Domainp_iff)
  then have "set_H z' \<subseteq> set_H z"
    unfolding H.axiom10_H by auto
  moreover have "map_H fst z' = map_H fst z"
    apply (rule sym)
    apply (subst H.rel_eq[symmetric])
    apply (subst H.rel_map(2))
    apply (rule H.rel_mono_strong)
     apply (fact \<open>rel_H ?L (map_H fst z) z'\<close>)
    apply (simp add: Grp_apply)
    done
  moreover have "map_H snd z' = map_H snd z"
    apply (subst H.rel_eq[symmetric])
    apply (subst H.rel_map(1))
    apply (rule H.rel_mono_strong)
     apply (fact \<open>rel_H ?L' z' (map_H snd z)\<close>)
    apply (simp add: Grp_apply)
    done
  moreover note \<open>Q z'\<close>
  ultimately show thesis using that by blast
qed

end
