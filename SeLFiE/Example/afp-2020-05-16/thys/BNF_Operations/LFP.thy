(*  Title:       LFP
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Least Fixpoint (a.k.a. Datatype)\<close>

(*<*)
theory LFP
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

ML \<open>open Ctr_Sugar_Util\<close>
notation BNF_Def.convol ("<_ , _>")

text \<open>
\begin{tabular}{rcl}
  'b1 &=& ('a, 'b1, 'b2) F1\\
  'b2 &=& ('a, 'b1, 'b2) F2
\end{tabular}

To build a witness scenario, let us assume

\begin{tabular}{rcl}
  ('a, 'b1, 'b2) F1 &=& 'a * 'b1 + 'a * 'b2\\
  ('a, 'b1, 'b2) F2 &=& unit + 'b1 * 'b2
\end{tabular}
\<close>

declare [[bnf_internals]]
bnf_axiomatization (F1set1: 'a, F1set2: 'b1, F1set3: 'b2)  F1
  [wits: "'a \<Rightarrow> 'b1 \<Rightarrow> ('a, 'b1, 'b2) F1" "'a \<Rightarrow> 'b2 \<Rightarrow> ('a, 'b1, 'b2) F1"]
  for map: F1map rel: F1rel
bnf_axiomatization (F2set1: 'a, F2set2: 'b1, F2set3: 'b2)  F2
  [wits: "('a, 'b1, 'b2) F2"]
  for map: F2map rel: F2rel


abbreviation F1in :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('a1, 'a2, 'a3) F1) set" where
  "F1in A1 A2 A3 \<equiv> {x. F1set1 x \<subseteq> A1 \<and> F1set2 x \<subseteq> A2 \<and> F1set3 x \<subseteq> A3}"
abbreviation F2in :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('a1, 'a2, 'a3) F2) set" where
  "F2in A1 A2 A3 \<equiv> {x. F2set1 x \<subseteq> A1 \<and> F2set2 x \<subseteq> A2 \<and> F2set3 x \<subseteq> A3}"

lemma F1map_comp_id: "F1map g1 g2 g3 (F1map id f2 f3 x) = F1map g1 (g2 o f2) (g3 o f3) x"
  apply (rule trans)
   apply (rule F1.map_comp)
  unfolding o_id
  apply (rule refl)
  done

lemmas F1in_mono23 = F1.in_mono[OF subset_refl]

lemma F1map_congL: "\<lbrakk>\<forall>a \<in> F1set2 x. f a = a; \<forall>a \<in> F1set3 x. g a = a\<rbrakk> \<Longrightarrow>
  F1map id f g x = x"
  apply (rule trans)
   apply (rule F1.map_cong0)
     apply (rule refl)
    apply (rule trans)
     apply (erule bspec)
     apply assumption
    apply (rule sym)
    apply (rule id_apply)
   apply (rule trans)
    apply (erule bspec)
    apply assumption
   apply (rule sym)
   apply (rule id_apply)
  apply (rule F1.map_id)
  done

lemma F2map_comp_id: "F2map g1 g2 g3 (F2map id f2 f3 x) = F2map g1 (g2 o f2) (g3 o f3) x"
  apply (rule trans)
   apply (rule F2.map_comp)
  unfolding o_id
  apply (rule refl)
  done

lemmas F2in_mono23 = F2.in_mono[OF subset_refl]

lemma F2map_congL: "\<lbrakk>\<forall>a \<in> F2set2 x. f a = a; \<forall>a \<in> F2set3 x. g a = a\<rbrakk> \<Longrightarrow>
  F2map id f g x = x"
  apply (rule trans)
   apply (rule F2.map_cong0)
     apply (rule refl)
    apply (rule trans)
     apply (erule bspec)
     apply assumption
    apply (rule sym)
    apply (rule id_apply)
   apply (rule trans)
    apply (erule bspec)
    apply assumption
   apply (rule sym)
   apply (rule id_apply)
  apply (rule F2.map_id)
  done


subsection\<open>Algebra\<close>

definition alg where
  "alg B1 B2 s1 s2 =
    ((\<forall>x \<in> F1in (UNIV :: 'a set) B1 B2. s1 x \<in> B1) \<and> (\<forall>y \<in> F2in (UNIV :: 'a set) B1 B2. s2 y \<in> B2))"

lemma alg_F1set: "\<lbrakk>alg B1 B2 s1 s2; F1set2 x \<subseteq> B1; F1set3 x \<subseteq> B2\<rbrakk> \<Longrightarrow> s1 x \<in> B1"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF alg_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply (rule CollectI)
  apply (rule conjI[OF subset_UNIV])
  apply (erule conjI)
  apply assumption
  done

lemma alg_F2set: "\<lbrakk>alg B1 B2 s1 s2; F2set2 x \<subseteq> B1; F2set3 x \<subseteq> B2\<rbrakk> \<Longrightarrow> s2 x \<in> B2"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF alg_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply (rule CollectI)
  apply (rule conjI[OF subset_UNIV])
  apply (erule conjI)
  apply assumption
  done

lemma alg_not_empty:
  "alg B1 B2 s1 s2 \<Longrightarrow> B1 \<noteq> {} \<and> B2 \<noteq> {}"
  apply (rule conjI)
   apply (rule notI)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (frule alg_F1set)

(* ORELSE of the following three possibilities *)

     apply (rule subset_emptyI)
     apply (erule F1.wit1 F1.wit2 F2.wit)

    apply (rule subsetI)
    apply (drule F1.wit1 F1.wit2 F2.wit)

(**)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (tactic \<open>FIRST' (map (fn thm => rtac @{context} thm THEN' assume_tac @{context}) @{thms alg_F1set alg_F2set}) 1\<close>)

     apply (rule subset_emptyI)
     apply (erule F1.wit1 F1.wit2 F2.wit)

    apply (rule subsetI)
    apply (drule F1.wit1 F1.wit2 F2.wit)
    apply (erule FalseE)
    (**)

   apply (erule emptyE)

  apply (rule notI)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (drule alg_F2set)

    apply (rule subsetI)
    apply (rule FalseE)
    apply (erule F1.wit1 F1.wit2 F2.wit)

   apply (rule subset_emptyI)
   apply (erule F1.wit1 F1.wit2 F2.wit)

  apply (erule emptyE)
  done


subsection \<open>Morphism\<close>

definition mor where
  "mor B1 B2 s1 s2 B1' B2' s1' s2' f g =
   (((\<forall>a \<in> B1. f a \<in> B1') \<and> (\<forall>a \<in> B2. g a \<in> B2')) \<and>
   ((\<forall>z \<in> F1in (UNIV :: 'a set) B1 B2. f (s1 z) = s1' (F1map id f g z)) \<and>
     (\<forall>z \<in> F2in (UNIV :: 'a set) B1 B2. g (s2 z) = s2' (F2map id f g z))))"

lemma morE1: "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g; z \<in> F1in UNIV B1 B2\<rbrakk>
   \<Longrightarrow> f (s1 z) = s1' (F1map id f g z)"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply assumption
  done

lemma morE2: "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g; z \<in> F2in UNIV B1 B2\<rbrakk>
   \<Longrightarrow> g (s2 z) = s2' (F2map id f g z)"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply assumption
  done

lemma mor_incl: "\<lbrakk>B1 \<subseteq> B1'; B2 \<subseteq> B2'\<rbrakk> \<Longrightarrow> mor B1 B2 s1 s2 B1' B2' s1 s2 id id"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)

   apply (rule conjI)
    apply (rule ballI)
    apply (erule subsetD)
    apply (erule ssubst_mem[OF id_apply])

   apply (rule ballI)
   apply (erule subsetD)
   apply (erule ssubst_mem[OF id_apply])

  apply (rule conjI)
   apply (rule ballI)
   apply (rule trans)
    apply (rule id_apply)
   apply (tactic \<open>stac @{context} @{thm F1.map_id} 1\<close>)
   apply (rule refl)

  apply (rule ballI)
  apply (rule trans)
   apply (rule id_apply)
  apply (tactic \<open>stac @{context} @{thm F2.map_id} 1\<close>)
  apply (rule refl)
  done

lemma mor_comp:
  "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g;
    mor B1' B2' s1' s2' B1'' B2'' s1'' s2'' f' g'\<rbrakk> \<Longrightarrow>
   mor B1 B2 s1 s2 B1'' B2'' s1'' s2'' (f' o f) (g' o g)"
  apply (tactic \<open>dtac @{context} (@{thm mor_def} RS iffD1) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm mor_def} RS iffD1) 1\<close>)
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (erule conjE)+
  apply (rule conjI)

   apply (rule conjI)
    apply (rule ballI)
    apply (rule ssubst_mem[OF o_apply])
    apply (erule bspec)
    apply (erule bspec)
    apply assumption

   apply (rule ballI)
   apply (rule ssubst_mem[OF o_apply])
   apply (erule bspec)
   apply (erule bspec)
   apply assumption

  apply (rule conjI)
   apply (rule ballI)
   apply (rule trans[OF o_apply])
   apply (rule trans)
    apply (rule trans)
     apply (drule bspec[rotated])
      apply assumption
     apply (erule arg_cong)
    apply (erule CollectE conjE)+
    apply (erule bspec)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule subset_UNIV)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(2))
     apply (rule image_subsetI)
     apply (erule bspec)
     apply (erule subsetD)
     apply assumption
    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(3))
    apply (rule image_subsetI)
    apply (erule bspec)
    apply (erule subsetD)
    apply assumption
   apply (rule arg_cong[OF F1map_comp_id])

  apply (rule ballI)
  apply (rule trans[OF o_apply])
  apply (rule trans)
   apply (rule trans)
    apply (drule bspec[rotated])
     apply assumption
    apply (erule arg_cong)
   apply (erule CollectE conjE)+
   apply (erule bspec)
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule subset_UNIV)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(2))
    apply (rule image_subsetI)
    apply (erule bspec)
    apply (erule subsetD)
    apply assumption
   apply (rule ord_eq_le_trans)
    apply (rule F2.set_map(3))
   apply (rule image_subsetI)
   apply (erule bspec)
   apply (erule subsetD)
   apply assumption
  apply (rule arg_cong[OF F2map_comp_id])
  done

lemma mor_cong: "\<lbrakk> f' = f; g' = g; mor B1 B2 s1 s2 B1' B2' s1' s2' f g\<rbrakk> \<Longrightarrow>
  mor B1 B2 s1 s2 B1' B2' s1' s2' f' g'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma mor_str:
  "mor UNIV UNIV (F1map id s1 s2) (F2map id s1 s2) UNIV UNIV s1 s2 s1 s2"
  apply (rule iffD2)
   apply (rule mor_def)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
   apply (rule UNIV_I)

  apply (rule conjI)
   apply (rule ballI)
   apply (rule refl)
  apply (rule ballI)
  apply (rule refl)
  done


subsection\<open>Bounds\<close>

type_synonym bd_type_F1' = "bd_type_F1 + (bd_type_F1, bd_type_F1, bd_type_F1) F1"
type_synonym bd_type_F2' = "bd_type_F2 + (bd_type_F2, bd_type_F2, bd_type_F2) F2"
type_synonym SucFbd_type = "((bd_type_F1' + bd_type_F2') set)"
type_synonym 'a1 ASucFbd_type = "(SucFbd_type \<Rightarrow> ('a1 + bool))"

abbreviation "F1bd' \<equiv> bd_F1 +c |UNIV :: (bd_type_F1, bd_type_F1, bd_type_F1) F1 set|"
lemma F1set1_bd_incr: "\<And>x. |F1set1 x| \<le>o F1bd'"
  by (rule ordLeq_transitive[OF F1.set_bd(1) ordLeq_csum1[OF F1.bd_Card_order]])
lemma F1set2_bd_incr: "\<And>x. |F1set2 x| \<le>o F1bd'"
  by (rule ordLeq_transitive[OF F1.set_bd(2) ordLeq_csum1[OF F1.bd_Card_order]])
lemma F1set3_bd_incr: "\<And>x. |F1set3 x| \<le>o F1bd'"
  by (rule ordLeq_transitive[OF F1.set_bd(3) ordLeq_csum1[OF F1.bd_Card_order]])

lemmas F1bd'_Card_order = Card_order_csum
lemmas F1bd'_Cinfinite = Cinfinite_csum1[OF F1.bd_Cinfinite]
lemmas F1bd'_Cnotzero = Cinfinite_Cnotzero[OF F1bd'_Cinfinite]
lemmas F1bd'_card_order = card_order_csum[OF F1.bd_card_order card_of_card_order_on]

abbreviation "F2bd' \<equiv> bd_F2 +c |UNIV :: (bd_type_F2, bd_type_F2, bd_type_F2) F2 set|"
lemma F2set1_bd_incr: "\<And>x. |F2set1 x| \<le>o F2bd'"
  by (rule ordLeq_transitive[OF F2.set_bd(1) ordLeq_csum1[OF F2.bd_Card_order]])
lemma F2set2_bd_incr: "\<And>x. |F2set2 x| \<le>o F2bd'"
  by (rule ordLeq_transitive[OF F2.set_bd(2) ordLeq_csum1[OF F2.bd_Card_order]])
lemma F2set3_bd_incr: "\<And>x. |F2set3 x| \<le>o F2bd'"
  by (rule ordLeq_transitive[OF F2.set_bd(3) ordLeq_csum1[OF F2.bd_Card_order]])

lemmas F2bd'_Card_order = Card_order_csum
lemmas F2bd'_Cinfinite = Cinfinite_csum1[OF F2.bd_Cinfinite]
lemmas F2bd'_Cnotzero = Cinfinite_Cnotzero[OF F2bd'_Cinfinite]
lemmas F2bd'_card_order = card_order_csum[OF F2.bd_card_order card_of_card_order_on]

abbreviation SucFbd where "SucFbd \<equiv> cardSuc (F1bd' +c F2bd')"
abbreviation ASucFbd where "ASucFbd \<equiv> ( |UNIV| +c ctwo ) ^c SucFbd"

lemma F1set1_bd: "|F1set1 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F1.set_bd(1))
  apply (rule ordLeq_csum1)
  apply (rule F1.bd_Card_order)
  done

lemma F1set2_bd: "|F1set2 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F1.set_bd(2))
  apply (rule ordLeq_csum1)
  apply (rule F1.bd_Card_order)
  done

lemma F1set3_bd: "|F1set3 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F1.set_bd(3))
  apply (rule ordLeq_csum1)
  apply (rule F1.bd_Card_order)
  done

lemma F2set1_bd: "|F2set1 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F2.set_bd(1))
  apply (rule ordLeq_csum2)
  apply (rule F2.bd_Card_order)
  done

lemma F2set2_bd: "|F2set2 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F2.set_bd(2))
  apply (rule ordLeq_csum2)
  apply (rule F2.bd_Card_order)
  done

lemma F2set3_bd: "|F2set3 x| \<le>o bd_F1 +c bd_F2"
  apply (rule ordLeq_transitive)
   apply (rule F2.set_bd(3))
  apply (rule ordLeq_csum2)
  apply (rule F2.bd_Card_order)
  done

lemmas SucFbd_Card_order = cardSuc_Card_order[OF Card_order_csum]
lemmas SucFbd_Cinfinite = Cinfinite_cardSuc[OF Cinfinite_csum1[OF F1bd'_Cinfinite]]
lemmas SucFbd_Cnotzero = Cinfinite_Cnotzero[OF SucFbd_Cinfinite]
lemmas worel_SucFbd = Card_order_wo_rel[OF SucFbd_Card_order]
lemmas ASucFbd_Cinfinite = Cinfinite_cexp[OF ordLeq_csum2[OF Card_order_ctwo] SucFbd_Cinfinite]


subsection\<open>Minimal Algebras\<close>

(* These are algebras generated by the empty set. *)
abbreviation min_G1 where
  "min_G1 As1_As2 i \<equiv> (\<Union>j \<in> underS SucFbd i. fst (As1_As2 j))"

abbreviation min_G2 where
  "min_G2 As1_As2 i \<equiv> (\<Union>j \<in> underS SucFbd i. snd (As1_As2 j))"

abbreviation min_H where
  "min_H s1 s2 As1_As2 i \<equiv>
    (min_G1 As1_As2 i \<union> s1 ` (F1in (UNIV :: 'a set) (min_G1 As1_As2 i) (min_G2 As1_As2 i)),
    min_G2 As1_As2 i \<union> s2 ` (F2in (UNIV :: 'a set) (min_G1 As1_As2 i) (min_G2 As1_As2 i)))"

abbreviation min_algs where
  "min_algs s1 s2 \<equiv> wo_rel.worec SucFbd (min_H s1 s2)"

definition min_alg1 where
  "min_alg1 s1 s2 = (\<Union>i \<in> Field SucFbd. fst (min_algs s1 s2 i))"

definition min_alg2 where
  "min_alg2 s1 s2 = (\<Union>i \<in> Field SucFbd. snd (min_algs s1 s2 i))"

lemma min_algs:
  "i \<in> Field SucFbd \<Longrightarrow> min_algs s1 s2 i = min_H s1 s2 (min_algs s1 s2) i"
  apply (rule fun_cong[OF wo_rel.worec_fixpoint[OF worel_SucFbd]])
  apply (rule iffD2)
   apply (rule meta_eq_to_obj_eq)
   apply (rule wo_rel.adm_wo_def[OF worel_SucFbd])
  apply (rule allI)+
  apply (rule impI)

  apply (rule iffD2)
   apply (rule prod.inject)
  apply (rule conjI)

   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule SUP_cong)
     apply (rule refl)
    apply (drule bspec)
     apply assumption
    apply (erule arg_cong)

   apply (rule image_cong)
    apply (rule arg_cong2[of _ _ _ _ "F1in UNIV"])
     apply (rule SUP_cong)
      apply (rule refl)
     apply (drule bspec)
      apply assumption
     apply (erule arg_cong)
    apply (rule SUP_cong)
     apply (rule refl)
    apply (drule bspec)
     apply assumption
    apply (erule arg_cong)
   apply (rule refl)

  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule SUP_cong)
    apply (rule refl)
   apply (drule bspec)
    apply assumption
   apply (erule arg_cong)

  apply (rule image_cong)
   apply (rule arg_cong2[of _ _ _ _ "F2in UNIV"])
    apply (rule SUP_cong)
     apply (rule refl)
    apply (drule bspec)
     apply assumption
    apply (erule arg_cong)
   apply (rule SUP_cong)
    apply (rule refl)
   apply (drule bspec)
    apply assumption
   apply (erule arg_cong)
  apply (rule refl)
  done

corollary min_algs1: "i \<in> Field SucFbd \<Longrightarrow> fst (min_algs s1 s2 i) =
  min_G1 (min_algs s1 s2) i \<union>
    s1 ` (F1in UNIV (min_G1 (min_algs s1 s2) i) (min_G2 (min_algs s1 s2) i))"
  apply (rule trans)
   apply (erule arg_cong[OF min_algs])
  apply (rule fst_conv)
  done

corollary min_algs2: "i \<in> Field SucFbd \<Longrightarrow> snd (min_algs s1 s2 i) =
  min_G2 (min_algs s1 s2) i \<union>
    s2 ` (F2in UNIV (min_G1 (min_algs s1 s2) i) (min_G2 (min_algs s1 s2) i))"
  apply (rule trans)
   apply (erule arg_cong[OF min_algs])
  apply (rule snd_conv)
  done

lemma min_algs_mono1: "relChain SucFbd (%i. fst (min_algs s1 s2 i))"
  apply (tactic \<open>rtac @{context} @{thm iffD2[OF meta_eq_to_obj_eq[OF relChain_def]]} 1\<close>)
  apply (rule allI)+
  apply (rule impI)
  apply (rule case_split)
   apply (rule xt1(3))
    apply (rule min_algs1)
    apply (erule FieldI2)
   apply (rule subsetI)
   apply (rule UnI1)
   apply (rule UN_I)
    apply (erule underS_I)
    apply assumption
   apply assumption
  apply (rule equalityD1)
  apply (drule notnotD)
  apply (erule arg_cong)
  done

lemma min_algs_mono2: "relChain SucFbd (%i. snd (min_algs s1 s2 i))"
  apply (tactic \<open>rtac @{context} @{thm iffD2[OF meta_eq_to_obj_eq[OF relChain_def]]} 1\<close>)
  apply (rule allI)+
  apply (rule impI)
  apply (rule case_split)
   apply (rule xt1(3))
    apply (rule min_algs2)
    apply (erule FieldI2)
   apply (rule subsetI)
   apply (rule UnI1)
   apply (rule UN_I)
    apply (erule underS_I)
    apply assumption
   apply assumption
  apply (rule equalityD1)
  apply (drule notnotD)
  apply (erule arg_cong)
  done

lemma SucFbd_limit: "\<lbrakk>x1 \<in> Field SucFbd & x2 \<in> Field SucFbd\<rbrakk>
 \<Longrightarrow> \<exists>y \<in> Field SucFbd. (x1 \<noteq> y \<and> (x1, y) \<in> SucFbd) \<and> (x2 \<noteq> y \<and> (x2, y) \<in> SucFbd)"
  apply (erule conjE)+
  apply (rule rev_mp)
   apply (rule Cinfinite_limit_finite)
     apply (rule finite.insertI)
     apply (rule finite.insertI)
     apply (rule finite.emptyI)
    apply (erule insert_subsetI)
    apply (erule insert_subsetI)
    apply (rule empty_subsetI)
   apply (rule SucFbd_Cinfinite)
  apply (rule impI)
  apply (erule bexE)
  apply (rule bexI)

   apply (rule conjI)

    apply (erule bspec)
    apply (rule insertI1)

   apply (erule bspec)
   apply (rule insertI2)
   apply (rule insertI1)
  apply assumption
  done

lemma alg_min_alg: "alg (min_alg1 s1 s2) (min_alg2 s1 s2) s1 s2"
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (erule CollectE conjE)+

   apply (rule bexE)
    apply (rule cardSuc_UNION_Cinfinite)
       apply (rule Cinfinite_csum1) (*TRY*)
       apply (rule F1bd'_Cinfinite)
      apply (rule min_algs_mono1)
     apply (erule subset_trans[OF _ equalityD1[OF min_alg1_def]])
    apply (rule ordLeq_transitive)
     apply (rule F1set2_bd_incr)
    apply (rule ordLeq_csum1) (*or refl *)
    apply (rule F1bd'_Card_order)

   apply (rule bexE)
    apply (rule cardSuc_UNION_Cinfinite)
       apply (rule Cinfinite_csum1) (*TRY*)
       apply (rule F1bd'_Cinfinite)
      apply (rule min_algs_mono2)
     apply (erule subset_trans[OF _ equalityD1[OF min_alg2_def]])
    apply (rule ordLeq_transitive)
     apply (rule F1set3_bd_incr)
    apply (rule ordLeq_csum1) (*or refl *)
    apply (rule F1bd'_Card_order)

   apply (rule bexE)
    apply (rule SucFbd_limit)
    apply (erule conjI)
    apply assumption
   apply (rule subsetD[OF equalityD2[OF min_alg1_def]])
   apply (rule UN_I)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl) (* m + 3 * n *)
    apply assumption
   apply (rule subsetD)
    apply (rule equalityD2)
    apply (rule min_algs1)
    apply assumption
   apply (rule UnI2)
   apply (rule image_eqI)
    apply (rule refl)
   apply (rule CollectI)
   apply (drule asm_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule conjE)+

   apply (rule conjI)
    apply assumption

   apply (rule conjI)
    apply (erule subset_trans)
    apply (rule subsetI)
    apply (rule UN_I)
     apply (erule underS_I)
     apply assumption
    apply assumption

   apply (erule subset_trans)
   apply (erule UN_upper[OF underS_I])
   apply assumption

(**)

  apply (rule ballI)
  apply (erule CollectE conjE)+

  apply (rule bexE)
   apply (rule cardSuc_UNION_Cinfinite)
      apply (rule Cinfinite_csum1) (*TRY*)
      apply (rule F1bd'_Cinfinite)
     apply (rule min_algs_mono1)

    apply (erule subset_trans[OF _ equalityD1[OF min_alg1_def]])
   apply (rule ordLeq_transitive)
    apply (rule F2set2_bd_incr)
   apply (rule ordLeq_csum2)
   apply (rule F2bd'_Card_order)

  apply (rule bexE)
   apply (rule cardSuc_UNION_Cinfinite)
      apply (rule Cinfinite_csum1) (*TRY*)
      apply (rule F1bd'_Cinfinite)
     apply (rule min_algs_mono2)

    apply (erule subset_trans[OF _ equalityD1[OF min_alg2_def]])
   apply (rule ordLeq_transitive)
    apply (rule F2set3_bd_incr)
   apply (rule ordLeq_csum2)
   apply (rule F2bd'_Card_order)

  apply (rule bexE)
   apply (rule SucFbd_limit)
   apply (erule conjI)
   apply assumption
  apply (rule subsetD[OF equalityD2[OF min_alg2_def]])
  apply (rule UN_I)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl) (* m + 3 * n *)
   apply assumption
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule min_algs2)
   apply assumption
  apply (rule UnI2)
  apply (rule image_eqI)
   apply (rule refl)
  apply (rule CollectI)
  apply (rule conjI)
   apply assumption

  apply (erule thin_rl)
  apply (erule thin_rl)
  apply (erule thin_rl)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule subset_trans)
   apply (rule UN_upper)
   apply (erule underS_I)
   apply assumption

  apply (erule subset_trans)
  apply (rule UN_upper)
  apply (erule underS_I)
  apply assumption
  done

lemmas SucFbd_ASucFbd = ordLess_ordLeq_trans[OF
    ordLess_ctwo_cexp
    cexp_mono1[OF ordLeq_csum2[OF Card_order_ctwo]],
    OF SucFbd_Card_order SucFbd_Card_order]

lemma card_of_min_algs:
  fixes s1 :: "('a, 'b, 'c) F1 \<Rightarrow> 'b" and s2 :: "('a, 'b, 'c) F2 \<Rightarrow> 'c"
  shows "i \<in> Field SucFbd \<longrightarrow>
  ( |fst (min_algs s1 s2 i)| \<le>o (ASucFbd :: 'a ASucFbd_type rel) \<and> |snd (min_algs s1 s2 i)| \<le>o (ASucFbd :: 'a ASucFbd_type rel) )"
  apply (rule well_order_induct_imp[of _ "%i. ( |fst (min_algs s1 s2 i)| \<le>o ASucFbd \<and> |snd (min_algs s1 s2 i)| \<le>o ASucFbd )", OF worel_SucFbd])
  apply (rule impI)
  apply (rule conjI)
   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (erule min_algs1)
   apply (rule Un_Cinfinite_bound)

     apply (rule UNION_Cinfinite_bound)

       apply (rule ordLess_imp_ordLeq)
       apply (rule ordLess_transitive)
        apply (rule card_of_underS)
         apply (rule SucFbd_Card_order)
        apply assumption
       apply (rule SucFbd_ASucFbd)

      apply (rule ballI)
      apply (erule allE)
      apply (drule mp)
       apply (erule underS_E)
      apply (drule mp)
       apply (erule underS_Field)
      apply (erule conjE)+
      apply assumption

     apply (rule ASucFbd_Cinfinite)

    apply (rule ordLeq_transitive)
     apply (rule card_of_image)
    apply (rule ordLeq_transitive)
     apply (rule F1.in_bd)
    apply (rule ordLeq_transitive)
     apply (rule cexp_mono1)
      apply (rule csum_mono1)
      apply (rule csum_mono2) (* REPEAT m *)
      apply (rule csum_cinfinite_bound)
          apply (rule UNION_Cinfinite_bound)

            apply (rule ordLess_imp_ordLeq)
            apply (rule ordLess_transitive)
             apply (rule card_of_underS)
              apply (rule SucFbd_Card_order)
             apply assumption
            apply (rule SucFbd_ASucFbd)

           apply (rule ballI)
           apply (erule allE)
           apply (drule mp)
            apply (erule underS_E)
           apply (drule mp)
            apply (erule underS_Field)
           apply (erule conjE)+
           apply assumption

          apply (rule ASucFbd_Cinfinite)

         apply (rule UNION_Cinfinite_bound)

           apply (rule ordLess_imp_ordLeq)
           apply (rule ordLess_transitive)
            apply (rule card_of_underS)
             apply (rule SucFbd_Card_order)
            apply assumption
           apply (rule SucFbd_ASucFbd)

          apply (rule ballI)
          apply (erule allE)
          apply (drule mp)
           apply (erule underS_E)
          apply (drule mp)
           apply (erule underS_Field)
          apply (erule conjE)+
          apply assumption

         apply (rule ASucFbd_Cinfinite)

        apply (rule card_of_Card_order)
       apply (rule card_of_Card_order)
      apply (rule ASucFbd_Cinfinite)

     apply (rule F1bd'_Card_order)
    apply (rule ordIso_ordLeq_trans)
     apply (rule cexp_cong1)
      apply (rule ordIso_transitive)
       apply (rule csum_cong1)
       apply (rule ordIso_transitive)
        apply (tactic \<open>BNF_Tactics.mk_rotate_eq_tac @{context}
           (rtac @{context} @{thm ordIso_refl} THEN'
           FIRST' [rtac @{context} @{thm card_of_Card_order},
           rtac @{context} @{thm Card_order_csum},
           rtac @{context} @{thm Card_order_cexp}])
           @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
           [1,2] [2,1] 1\<close>)
       apply (rule csum_absorb1)
        apply (rule ASucFbd_Cinfinite)

       apply (rule ordLeq_transitive)
        apply (rule ordLeq_csum1)
        apply (tactic \<open>FIRST' [rtac @{context} @{thm Card_order_csum}, rtac @{context} @{thm card_of_Card_order}] 1\<close>)
       apply (rule ordLeq_cexp1)
        apply (rule SucFbd_Cnotzero)
       apply (rule Card_order_csum)
      apply (rule csum_absorb1)
       apply (rule ASucFbd_Cinfinite)
      apply (rule ctwo_ordLeq_Cinfinite)
      apply (rule ASucFbd_Cinfinite)
     apply (rule F1bd'_Card_order)
    apply (rule ordIso_imp_ordLeq)
    apply (rule cexp_cprod_ordLeq)

       apply (rule Card_order_csum)
      apply (rule SucFbd_Cinfinite)
     apply (rule F1bd'_Cnotzero)
    apply (rule ordLeq_transitive)
     apply (rule ordLeq_csum1)
     apply (rule F1bd'_Card_order)
    apply (rule cardSuc_ordLeq)
    apply (rule Card_order_csum)

   apply (rule ASucFbd_Cinfinite)

  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst)
   apply (erule min_algs2)
  apply (rule Un_Cinfinite_bound)

    apply (rule UNION_Cinfinite_bound)

      apply (rule ordLess_imp_ordLeq)
      apply (rule ordLess_transitive)
       apply (rule card_of_underS)
        apply (rule SucFbd_Card_order)
       apply assumption
      apply (rule SucFbd_ASucFbd)

     apply (rule ballI)
     apply (erule allE)
     apply (drule mp)
      apply (erule underS_E)
     apply (drule mp)
      apply (erule underS_Field)
     apply (erule conjE)+
     apply assumption

    apply (rule ASucFbd_Cinfinite)

   apply (rule ordLeq_transitive)
    apply (rule card_of_image)
   apply (rule ordLeq_transitive)
    apply (rule F2.in_bd)
   apply (rule ordLeq_transitive)
    apply (rule cexp_mono1)
     apply (rule csum_mono1)
     apply (rule csum_mono2)
     apply (rule csum_cinfinite_bound)
         apply (rule UNION_Cinfinite_bound)

           apply (rule ordLess_imp_ordLeq)
           apply (rule ordLess_transitive)
            apply (rule card_of_underS)
             apply (rule SucFbd_Card_order)
            apply assumption
           apply (rule SucFbd_ASucFbd)

          apply (rule ballI)
          apply (erule allE)
          apply (drule mp)
           apply (erule underS_E)
          apply (drule mp)
           apply (erule underS_Field)
          apply (erule conjE)+
          apply assumption

         apply (rule ASucFbd_Cinfinite)

        apply (rule UNION_Cinfinite_bound)

          apply (rule ordLess_imp_ordLeq)
          apply (rule ordLess_transitive)
           apply (rule card_of_underS)
            apply (rule SucFbd_Card_order)
           apply assumption
          apply (rule SucFbd_ASucFbd)

         apply (rule ballI)
         apply (erule allE)
         apply (drule mp)
          apply (erule underS_E)
         apply (drule mp)
          apply (erule underS_Field)
         apply (erule conjE)+
         apply assumption

        apply (rule ASucFbd_Cinfinite)

       apply (rule card_of_Card_order)
      apply (rule card_of_Card_order)
     apply (rule ASucFbd_Cinfinite)

    apply (rule F2bd'_Card_order)
   apply (rule ordIso_ordLeq_trans)
    apply (rule cexp_cong1)

     apply (rule ordIso_transitive)
      apply (rule csum_cong1)
      apply (rule ordIso_transitive)
       apply (tactic \<open>BNF_Tactics.mk_rotate_eq_tac @{context}
           (rtac @{context} @{thm ordIso_refl} THEN'
           FIRST' [rtac @{context} @{thm card_of_Card_order},
           rtac @{context} @{thm Card_order_csum},
           rtac @{context} @{thm Card_order_cexp}])
           @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
           [1,2] [2,1] 1\<close>)
      apply (rule csum_absorb1)
       apply (rule ASucFbd_Cinfinite)

      apply (rule ordLeq_transitive)
       apply (rule ordLeq_csum1)
       apply (tactic \<open>FIRST' [rtac @{context} @{thm Card_order_csum}, rtac @{context} @{thm card_of_Card_order}] 1\<close>)
      apply (rule ordLeq_cexp1)
       apply (rule SucFbd_Cnotzero)
      apply (rule Card_order_csum)

     apply (rule csum_absorb1)
      apply (rule ASucFbd_Cinfinite)
     apply (rule ctwo_ordLeq_Cinfinite)
     apply (rule ASucFbd_Cinfinite)
    apply (rule F2bd'_Card_order)
   apply (rule ordIso_imp_ordLeq)
   apply (rule cexp_cprod_ordLeq)
      apply (rule Card_order_csum)
     apply (rule SucFbd_Cinfinite)
    apply (rule F2bd'_Cnotzero)
   apply (rule ordLeq_transitive)
    apply (rule ordLeq_csum2)
    apply (rule F2bd'_Card_order)
   apply (rule cardSuc_ordLeq)
   apply (rule Card_order_csum)

  apply (rule ASucFbd_Cinfinite)
  done

lemma card_of_min_alg1:
  fixes s1 :: "('a, 'b, 'c) F1 \<Rightarrow> 'b" and s2 :: "('a, 'b, 'c) F2 \<Rightarrow> 'c"
  shows "|min_alg1 s1 s2| \<le>o (ASucFbd :: 'a ASucFbd_type rel)"
  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst[OF min_alg1_def])
  apply (rule UNION_Cinfinite_bound)

    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_Field_ordIso)
     apply (rule SucFbd_Card_order)
    apply (rule ordLess_imp_ordLeq)
    apply (rule SucFbd_ASucFbd)

   apply (rule ballI)
   apply (drule rev_mp)
    apply (rule card_of_min_algs)
   apply (erule conjE)+
   apply assumption
  apply (rule ASucFbd_Cinfinite)
  done

lemma card_of_min_alg2:
  fixes s1 :: "('a, 'b, 'c) F1 \<Rightarrow> 'b" and s2 :: "('a, 'b, 'c) F2 \<Rightarrow> 'c"
  shows "|min_alg2 s1 s2| \<le>o (ASucFbd :: 'a ASucFbd_type rel)"
  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst[OF min_alg2_def])
  apply (rule UNION_Cinfinite_bound)

    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_Field_ordIso)
     apply (rule SucFbd_Card_order)
    apply (rule ordLess_imp_ordLeq)
    apply (rule SucFbd_ASucFbd)

   apply (rule ballI)
   apply (drule rev_mp)
    apply (rule card_of_min_algs)
   apply (erule conjE)+
   apply assumption
  apply (rule ASucFbd_Cinfinite)
  done

lemma least_min_algs: "alg B1 B2 s1 s2 \<Longrightarrow>
  i \<in> Field SucFbd \<longrightarrow>
    fst (min_algs s1 s2 i) \<subseteq> B1 \<and> snd (min_algs s1 s2 i) \<subseteq> B2"
  apply (rule well_order_induct_imp[of _ "%i. (fst (min_algs s1 s2 i) \<subseteq> B1 \<and> snd (min_algs s1 s2 i) \<subseteq> B2)", OF worel_SucFbd])
  apply (rule impI)
  apply (rule conjI)
   apply (rule ord_eq_le_trans)
    apply (erule min_algs1)
   apply (rule Un_least)
    apply (rule UN_least)
    apply (erule allE)
    apply (drule mp)
     apply (erule underS_E)
    apply (drule mp)
     apply (erule underS_Field)
    apply (erule conjE)+
    apply assumption
   apply (rule image_subsetI)
   apply (erule CollectE conjE)+
   apply (erule alg_F1set)

    apply (erule subset_trans)
    apply (rule UN_least)
    apply (erule allE)
    apply (drule mp)
     apply (erule underS_E)
    apply (drule mp)
     apply (erule underS_Field)
    apply (erule conjE)+
    apply assumption

   apply (erule subset_trans)
   apply (rule UN_least)
   apply (erule allE)
   apply (drule mp)
    apply (erule underS_E)
   apply (drule mp)
    apply (erule underS_Field)
   apply (erule conjE)+
   apply assumption

  apply (rule ord_eq_le_trans)
   apply (erule min_algs2)
  apply (rule Un_least)
   apply (rule UN_least)
   apply (erule allE)
   apply (drule mp)
    apply (erule underS_E)
   apply (drule mp)
    apply (erule underS_Field)
   apply (erule conjE)+
   apply assumption
  apply (rule image_subsetI)
  apply (erule CollectE conjE)+
  apply (erule alg_F2set)

   apply (erule subset_trans)
   apply (rule UN_least)
   apply (erule allE)
   apply (drule mp)
    apply (erule underS_E)
   apply (drule mp)
    apply (erule underS_Field)
   apply (erule conjE)+
   apply assumption

  apply (erule subset_trans)
  apply (rule UN_least)
  apply (erule allE)
  apply (drule mp)
   apply (erule underS_E)
  apply (drule mp)
   apply (erule underS_Field)
  apply (erule conjE)+
  apply assumption
  done

lemma least_min_alg1: "alg B1 B2 s1 s2 \<Longrightarrow> min_alg1 s1 s2 \<subseteq> B1"
  apply (rule ord_eq_le_trans[OF min_alg1_def])
  apply (rule UN_least)
  apply (drule least_min_algs)
  apply (drule mp)
   apply assumption
  apply (erule conjE)+
  apply assumption
  done

lemma least_min_alg2: "alg B1 B2 s1 s2 \<Longrightarrow> min_alg2 s1 s2 \<subseteq> B2"
  apply (rule ord_eq_le_trans[OF min_alg2_def])
  apply (rule UN_least)
  apply (drule least_min_algs)
  apply (drule mp)
   apply assumption
  apply (erule conjE)+
  apply assumption
  done

lemma mor_incl_min_alg:
  "alg B1 B2 s1 s2 \<Longrightarrow>
   mor (min_alg1 s1 s2) (min_alg2 s1 s2) s1 s2 B1 B2 s1 s2 id id"
  apply (rule mor_incl)
   apply (erule least_min_alg1)
  apply (erule least_min_alg2)
  done

subsection \<open>Initiality\<close>

text\<open>The following ``happens" to be the type (for our particular construction)
of the initial algebra carrier:\<close>

type_synonym 'a1 F1init_type = "('a1, 'a1 ASucFbd_type, 'a1 ASucFbd_type) F1 \<Rightarrow> 'a1 ASucFbd_type"
type_synonym 'a1 F2init_type = "('a1, 'a1 ASucFbd_type, 'a1 ASucFbd_type) F2 \<Rightarrow> 'a1 ASucFbd_type"

typedef 'a1 IIT =
  "UNIV ::
    (('a1 ASucFbd_type set \<times> 'a1 ASucFbd_type set) \<times> ('a1 F1init_type \<times> 'a1 F2init_type)) set"
  by (rule exI) (rule UNIV_I)


subsection\<open>Initial Algebras\<close>

abbreviation II :: "'a1 IIT set" where
  "II \<equiv> {Abs_IIT ((B1, B2), (s1, s2)) |B1 B2 s1 s2. alg B1 B2 s1 s2}"
definition str_init1 where
  "str_init1 (dummy :: 'a1)
    (y::('a1, 'a1 IIT \<Rightarrow> 'a1 ASucFbd_type, 'a1 IIT \<Rightarrow> 'a1 ASucFbd_type) F1)
    (i :: 'a1 IIT) =
      fst (snd (Rep_IIT i))
        (F1map id (\<lambda>f :: 'a1 IIT \<Rightarrow> 'a1 ASucFbd_type. f i) (\<lambda>f. f i) y)"
definition str_init2 where
  "str_init2 (dummy :: 'a1) y (i :: 'a1 IIT) =
      snd (snd (Rep_IIT i)) (F2map id (\<lambda>f. f i) (\<lambda>f. f i) y)"
abbreviation car_init1 where
  "car_init1 dummy \<equiv> min_alg1 (str_init1 dummy) (str_init2 dummy)"
abbreviation car_init2 where
  "car_init2 dummy \<equiv> min_alg2 (str_init1 dummy) (str_init2 dummy)"

lemma alg_select:
  "\<forall>i \<in> II. alg (fst (fst (Rep_IIT i))) (snd (fst (Rep_IIT i)))
                      (fst (snd (Rep_IIT i))) (snd (snd (Rep_IIT i)))"
  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding fst_conv snd_conv Abs_IIT_inverse[OF UNIV_I]
  apply assumption
  done

lemma mor_select:
  "\<lbrakk>i \<in> II;
    mor (fst (fst (Rep_IIT i))) (snd (fst (Rep_IIT i)))
        (fst (snd (Rep_IIT i))) (snd (snd (Rep_IIT i))) UNIV UNIV s1' s2' f g\<rbrakk> \<Longrightarrow>
  mor (car_init1 dummy) (car_init2 dummy) (str_init1 dummy) (str_init2 dummy) UNIV UNIV s1' s2' (f \<circ> (\<lambda>h. h i)) (g \<circ> (\<lambda>h. h i))"
  apply (rule mor_cong)
    apply (rule sym)
    apply (rule o_id)
   apply (rule sym)
   apply (rule o_id)
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm mor_comp}) 1\<close>)
   apply (tactic \<open>etac @{context} (Thm.permute_prems 0 1 @{thm mor_comp}) 1\<close>)
   apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
   apply (rule conjI)

    apply (rule conjI)
     apply (rule ballI)
     apply (erule bspec[rotated])
     apply (erule CollectE)
     apply assumption

    apply (rule ballI)
    apply (erule bspec[rotated])
    apply (erule CollectE)
    apply assumption

   apply (rule conjI)
    apply (rule ballI)
    apply (rule str_init1_def)

   apply (rule ballI)
   apply (rule str_init2_def)

  apply (rule mor_incl_min_alg)
    (*alg_epi*)
  apply (erule thin_rl)+
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (rule CollectI)
   apply (rule ballI)
   apply (frule bspec[OF alg_select])
   apply (rule ssubst_mem[OF str_init1_def])
   apply (erule alg_F1set)

    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(2))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule image_Collect_subsetI)
    apply (erule bspec)
    apply assumption

   apply (rule ord_eq_le_trans)
    apply (rule F1.set_map(3))
   apply (rule subset_trans)
    apply (erule image_mono)
   apply (rule image_Collect_subsetI)
   apply (erule bspec)
   apply assumption


  apply (rule ballI)
  apply (erule CollectE conjE)+
  apply (rule CollectI)
  apply (rule ballI)
  apply (frule bspec[OF alg_select])
  apply (rule ssubst_mem[OF str_init2_def])
  apply (erule alg_F2set)

   apply (rule ord_eq_le_trans)
    apply (rule F2.set_map(2))
   apply (rule subset_trans)
    apply (erule image_mono)
   apply (rule image_Collect_subsetI)
   apply (erule bspec)
   apply assumption

  apply (rule ord_eq_le_trans)
   apply (rule F2.set_map(3))
  apply (rule subset_trans)
   apply (erule image_mono)
  apply (rule image_Collect_subsetI)
  apply (erule bspec)
  apply assumption
  done

lemma init_unique_mor:
  "\<lbrakk>a1 \<in> car_init1 dummy; a2 \<in> car_init2 dummy;
    mor (car_init1 dummy) (car_init2 dummy) (str_init1 dummy) (str_init2 dummy) B1 B2 s1 s2 f1 f2;
    mor (car_init1 dummy) (car_init2 dummy) (str_init1 dummy) (str_init2 dummy) B1 B2 s1 s2 g1 g2\<rbrakk> \<Longrightarrow>
  f1 a1 = g1 a1 \<and> f2 a2 = g2 a2"
  apply (rule conjI)
   apply (erule prop_restrict)
   apply (erule thin_rl)
   apply (rule least_min_alg1)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule CollectI)
    apply (erule CollectE conjE)+
    apply (rule conjI)

     apply (rule alg_F1set[OF alg_min_alg])
      apply (erule subset_trans)
      apply (rule Collect_restrict)
     apply (erule subset_trans)
     apply (rule Collect_restrict)

    apply (rule trans)
     apply (erule morE1)
     apply (rule subsetD)
      apply (rule F1in_mono23)
       apply (rule Collect_restrict)
      apply (rule Collect_restrict)
     apply (rule CollectI)
     apply (rule conjI)
      apply assumption
     apply (rule conjI)
      apply assumption
     apply assumption

    apply (rule trans)
     apply (rule arg_cong[OF F1.map_cong0])
       apply (rule refl)
      apply (erule prop_restrict)
      apply assumption
     apply (erule prop_restrict)
     apply assumption

    apply (rule sym)
    apply (erule morE1)
    apply (rule subsetD)
     apply (rule F1in_mono23)
      apply (rule Collect_restrict)
     apply (rule Collect_restrict)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply assumption
    apply assumption

   apply (rule ballI)
   apply (rule CollectI)
   apply (erule CollectE conjE)+
   apply (rule conjI)

    apply (rule alg_F2set[OF alg_min_alg])
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule trans)
    apply (erule morE2)
    apply (rule subsetD)
     apply (rule F2in_mono23)
      apply (rule Collect_restrict)
     apply (rule Collect_restrict)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply assumption
    apply assumption

   apply (rule trans)
    apply (rule arg_cong[OF F2.map_cong0])
      apply (rule refl)
     apply (erule prop_restrict)
     apply assumption
    apply (erule prop_restrict)
    apply assumption

   apply (rule sym)
   apply (erule morE2)
   apply (rule subsetD)
    apply (rule F2in_mono23)
     apply (rule Collect_restrict)
    apply (rule Collect_restrict)
   apply (rule CollectI)
   apply (rule conjI)
    apply assumption
   apply (rule conjI)
    apply assumption
   apply assumption


  apply (erule thin_rl)
  apply (erule prop_restrict)
  apply (rule least_min_alg2)
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule CollectI)
   apply (erule CollectE conjE)+
   apply (rule conjI)

    apply (rule alg_F1set[OF alg_min_alg])
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule trans)
    apply (erule morE1)
    apply (rule subsetD)
     apply (rule F1in_mono23)
      apply (rule Collect_restrict)
     apply (rule Collect_restrict)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply assumption
    apply assumption

   apply (rule trans)
    apply (rule arg_cong[OF F1.map_cong0])
      apply (rule refl)
     apply (erule prop_restrict)
     apply assumption
    apply (erule prop_restrict)
    apply assumption

   apply (rule sym)
   apply (erule morE1)
   apply (rule subsetD)
    apply (rule F1in_mono23)
     apply (rule Collect_restrict)
    apply (rule Collect_restrict)
   apply (rule CollectI)
   apply (rule conjI)
    apply assumption
   apply (rule conjI)
    apply assumption
   apply assumption

  apply (rule ballI)
  apply (rule CollectI)
  apply (erule CollectE conjE)+
  apply (rule conjI)

   apply (rule alg_F2set[OF alg_min_alg])
    apply (erule subset_trans)
    apply (rule Collect_restrict)
   apply (erule subset_trans)
   apply (rule Collect_restrict)

  apply (rule trans)
   apply (erule morE2)
   apply (rule subsetD)
    apply (rule F2in_mono23)
     apply (rule Collect_restrict)
    apply (rule Collect_restrict)
   apply (rule CollectI)
   apply (rule conjI)
    apply assumption
   apply (rule conjI)
    apply assumption
   apply assumption

  apply (rule trans)
   apply (rule arg_cong[OF F2.map_cong0])
     apply (rule refl)
    apply (erule prop_restrict)
    apply assumption
   apply (erule prop_restrict)
   apply assumption

  apply (rule sym)
  apply (erule morE2)
  apply (rule subsetD)
   apply (rule F2in_mono23)
    apply (rule Collect_restrict)
   apply (rule Collect_restrict)
  apply (rule CollectI)
  apply (rule conjI)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply assumption
  done

abbreviation closed where
  "closed dummy phi1 phi2 \<equiv> ((\<forall>x \<in> F1in UNIV (car_init1 dummy) (car_init2 dummy).
   (\<forall>z \<in> F1set2 x. phi1 z) \<and> (\<forall>z \<in> F1set3 x. phi2 z) \<longrightarrow> phi1 (str_init1 dummy x)) \<and>
     (\<forall>x \<in> F2in UNIV (car_init1 dummy) (car_init2 dummy).
   (\<forall>z \<in> F2set2 x. phi1 z) \<and> (\<forall>z \<in> F2set3 x. phi2 z) \<longrightarrow> phi2 (str_init2 dummy x)))"

lemma init_induct: "closed dummy phi1 phi2 \<Longrightarrow>
  (\<forall>x \<in> car_init1 dummy. phi1 x) \<and> (\<forall>x \<in> car_init2 dummy. phi2 x)"
  apply (rule conjI)
   apply (rule ballI)
   apply (erule prop_restrict)
   apply (rule least_min_alg1)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)

   apply (rule conjI)
    apply (rule ballI)
    apply (rule CollectI)
    apply (erule CollectE conjE)+
    apply (rule conjI)

     apply (rule alg_F1set[OF alg_min_alg])
      apply (erule subset_trans)
      apply (rule Collect_restrict)
     apply (erule subset_trans)
     apply (rule Collect_restrict)

    apply (rule mp)
     apply (erule bspec)
     apply (rule CollectI)
     apply (rule conjI)
      apply assumption
     apply (rule conjI)
      apply (erule subset_trans)
      apply (rule Collect_restrict)
     apply (erule subset_trans)
     apply (rule Collect_restrict)

    apply (rule conjI)
     apply (rule ballI)
     apply (erule prop_restrict)
     apply assumption
    apply (rule ballI)
    apply (erule prop_restrict)
    apply assumption


   apply (rule ballI)
   apply (rule CollectI)
   apply (erule CollectE conjE)+
   apply (rule conjI)

    apply (rule alg_F2set[OF alg_min_alg])
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule mp)
    apply (erule bspec)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule conjI)
    apply (rule ballI)
    apply (erule prop_restrict)
    apply assumption
   apply (rule ballI)
   apply (erule prop_restrict)
   apply assumption

  apply (rule ballI)
  apply (erule prop_restrict)
  apply (rule least_min_alg2)
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)

  apply (rule conjI)
   apply (rule ballI)
   apply (rule CollectI)
   apply (erule CollectE conjE)+
   apply (rule conjI)

    apply (rule alg_F1set[OF alg_min_alg])
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule mp)
    apply (erule bspec)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply (erule subset_trans)
     apply (rule Collect_restrict)
    apply (erule subset_trans)
    apply (rule Collect_restrict)

   apply (rule conjI)
    apply (rule ballI)
    apply (erule prop_restrict)
    apply assumption
   apply (rule ballI)
   apply (erule prop_restrict)
   apply assumption


  apply (rule ballI)
  apply (rule CollectI)
  apply (erule CollectE conjE)+
  apply (rule conjI)

   apply (rule alg_F2set[OF alg_min_alg])
    apply (erule subset_trans)
    apply (rule Collect_restrict)
   apply (erule subset_trans)
   apply (rule Collect_restrict)

  apply (rule mp)
   apply (erule bspec)
   apply (rule CollectI)
   apply (rule conjI)
    apply assumption
   apply (rule conjI)
    apply (erule subset_trans)
    apply (rule Collect_restrict)
   apply (erule subset_trans)
   apply (rule Collect_restrict)

  apply (rule conjI)
   apply (rule ballI)
   apply (erule prop_restrict)
   apply assumption
  apply (rule ballI)
  apply (erule prop_restrict)
  apply assumption
  done


subsection \<open>The datatype\<close>

typedef (overloaded) 'a1 IF1 = "car_init1 (undefined :: 'a1)"
  apply (rule iffD2)
   apply (rule ex_in_conv)
  apply (rule conjunct1)
  apply (rule alg_not_empty)
  apply (rule alg_min_alg)
  done

typedef (overloaded) 'a1 IF2 = "car_init2 (undefined :: 'a1)"
  apply (rule iffD2)
   apply (rule ex_in_conv)
  apply (rule conjunct2)
  apply (rule alg_not_empty)
  apply (rule alg_min_alg)
  done

definition ctor1 where "ctor1 = Abs_IF1 o str_init1 undefined o F1map id Rep_IF1 Rep_IF2"
definition ctor2 where "ctor2 = Abs_IF2 o str_init2 undefined o F2map id Rep_IF1 Rep_IF2"

lemma mor_Rep_IF:
  "mor (UNIV :: 'a IF1 set) (UNIV :: 'a IF2 set) ctor1 ctor2
     (car_init1 undefined) (car_init2 undefined) (str_init1 undefined) (str_init2 undefined) Rep_IF1 Rep_IF2"
  unfolding mor_def ctor1_def ctor2_def o_apply
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule Rep_IF1)
   apply (rule ballI)
   apply (rule Rep_IF2)

  apply (rule conjI)
   apply (rule ballI)
   apply (rule Abs_IF1_inverse)
   apply (rule alg_F1set[OF alg_min_alg])
    apply (rule ord_eq_le_trans[OF F1.set_map(2)])
    apply (rule image_subsetI)
    apply (rule Rep_IF1)
   apply (rule ord_eq_le_trans[OF F1.set_map(3)])
   apply (rule image_subsetI)
   apply (rule Rep_IF2)

  apply (rule ballI)
  apply (rule Abs_IF2_inverse)
  apply (rule alg_F2set[OF alg_min_alg])
   apply (rule ord_eq_le_trans[OF F2.set_map(2)])
   apply (rule image_subsetI)
   apply (rule Rep_IF1)
  apply (rule ord_eq_le_trans[OF F2.set_map(3)])
  apply (rule image_subsetI)
  apply (rule Rep_IF2)
  done

lemma mor_Abs_IF:
  "mor (car_init1 undefined) (car_init2 undefined)
    (str_init1 undefined) (str_init2 undefined) UNIV UNIV ctor1 ctor2 Abs_IF1 Abs_IF2"
  unfolding mor_def ctor1_def ctor2_def o_apply
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
   apply (rule UNIV_I)

  apply (rule conjI)
   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (rule sym[OF arg_cong[OF trans[OF F1map_comp_id F1map_congL]]])
    apply (rule ballI[OF trans[OF o_apply]])
    apply (erule Abs_IF1_inverse[OF subsetD])
    apply assumption
   apply (rule ballI[OF trans[OF o_apply]])
   apply (erule Abs_IF2_inverse[OF subsetD])
   apply assumption

  apply (rule ballI)
  apply (erule CollectE conjE)+
  apply (rule sym[OF arg_cong[OF trans[OF F2map_comp_id F2map_congL]]])
   apply (rule ballI[OF trans[OF o_apply]])
   apply (erule Abs_IF1_inverse[OF subsetD])
   apply assumption
  apply (rule ballI[OF trans[OF o_apply]])
  apply (erule Abs_IF2_inverse[OF subsetD])
  apply assumption
  done

lemma copy:
  "\<lbrakk>alg B1 B2 s1 s2; bij_betw f B1' B1; bij_betw g B2' B2\<rbrakk> \<Longrightarrow>
   \<exists>f' g'. alg B1' B2' f' g' \<and> mor B1' B2' f' g' B1 B2 s1 s2 f g"
  apply (rule exI)+
  apply (rule conjI)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
   apply (rule conjI)
    apply (rule ballI)
    apply (erule CollectE conjE)+
    apply (rule subsetD)
     apply (rule equalityD1)
     apply (erule bij_betw_imp_surj_on[OF bij_betw_the_inv_into])
    apply (rule imageI)
    apply (erule alg_F1set)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(2))
     apply (rule subset_trans)
      apply (erule image_mono)
     apply (rule equalityD1)
     apply (erule bij_betw_imp_surj_on)
    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(3))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule equalityD1)
    apply (erule bij_betw_imp_surj_on)

   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (rule subsetD)
    apply (rule equalityD1)
    apply (erule bij_betw_imp_surj_on[OF bij_betw_the_inv_into])
   apply (rule imageI)
   apply (erule alg_F2set)
    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(2))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule equalityD1)
    apply (erule bij_betw_imp_surj_on)
   apply (rule ord_eq_le_trans)
    apply (rule F2.set_map(3))
   apply (rule subset_trans)
    apply (erule image_mono)
   apply (rule equalityD1)
   apply (erule bij_betw_imp_surj_on)

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule conjI)
    apply (erule bij_betwE)
   apply (erule bij_betwE)

  apply (rule conjI)
   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (erule f_the_inv_into_f_bij_betw)
   apply (erule alg_F1set)
    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(2))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule equalityD1)
    apply (erule bij_betw_imp_surj_on)
   apply (rule ord_eq_le_trans)
    apply (rule F1.set_map(3))
   apply (rule subset_trans)
    apply (erule image_mono)
   apply (rule equalityD1)
   apply (erule bij_betw_imp_surj_on)

  apply (rule ballI)
  apply (erule CollectE conjE)+
  apply (erule f_the_inv_into_f_bij_betw)
  apply (erule alg_F2set)
   apply (rule ord_eq_le_trans)
    apply (rule F2.set_map(2))
   apply (rule subset_trans)
    apply (erule image_mono)
   apply (rule equalityD1)
   apply (erule bij_betw_imp_surj_on)
  apply (rule ord_eq_le_trans)
   apply (rule F2.set_map(3))
  apply (rule subset_trans)
   apply (erule image_mono)
  apply (rule equalityD1)
  apply (erule bij_betw_imp_surj_on)
  done

lemma init_ex_mor:
  "\<exists>f g. mor UNIV UNIV ctor1 ctor2 UNIV UNIV s1 s2 f g"
  apply (insert ex_bij_betw[OF card_of_min_alg1, of s1 s2]
      ex_bij_betw[OF card_of_min_alg2, of s1 s2])
  apply (erule exE)+
  apply (rule rev_mp)
   apply (rule copy[OF alg_min_alg])
    apply assumption
   apply assumption
  apply (rule impI)
  apply (erule exE conjE)+

  apply (rule exI)+
  apply (rule mor_comp)
   apply (rule mor_Rep_IF)
  apply (rule mor_select)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
  unfolding fst_conv snd_conv Abs_IIT_inverse[OF UNIV_I]
  apply (erule mor_comp)
  apply (rule mor_incl)
   apply (rule subset_UNIV)
  apply (rule subset_UNIV)
  done

text \<open>Iteration\<close>

abbreviation fold where
  "fold s1 s2 \<equiv> (SOME f. mor UNIV UNIV ctor1 ctor2 UNIV UNIV s1 s2 (fst f) (snd f))"

definition fold1 where "fold1 s1 s2 = fst (fold s1 s2)"
definition fold2 where "fold2 s1 s2 = snd (fold s1 s2)"

lemma mor_fold:
  "mor UNIV UNIV ctor1 ctor2 UNIV UNIV s1 s2 (fold1 s1 s2) (fold2 s1 s2)"
  unfolding fold1_def fold2_def
  apply (rule rev_mp)
   apply (rule init_ex_mor)
  apply (rule impI)
  apply (erule exE)
  apply (erule exE)
  apply (rule someI[of "%(f :: ('a IF1 \<Rightarrow> 'b) \<times> ('a IF2 \<Rightarrow> 'c)).
  mor UNIV UNIV ctor1 ctor2 UNIV UNIV s1 s2 (fst f) (snd f)"])
  apply (erule mor_cong[OF fst_conv snd_conv])
  done

ML \<open>
  val fold1 = rule_by_tactic @{context}
    (rtac @{context} CollectI 1 THEN BNF_Util.CONJ_WRAP (K (rtac @{context} @{thm subset_UNIV} 1)) (1 upto 3))
    @{thm morE1[OF mor_fold]}

  val fold2 = rule_by_tactic @{context}
    (rtac @{context} CollectI 1 THEN BNF_Util.CONJ_WRAP (K (rtac @{context} @{thm subset_UNIV} 1)) (1 upto 3))
    @{thm morE2[OF mor_fold]}
\<close>

theorem fold1:
  "(fold1 s1 s2) (ctor1 x) = s1 (F1map id (fold1 s1 s2) (fold2 s1 s2) x)"
  apply (rule morE1)
   apply (rule mor_fold)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule subset_UNIV)
  done

theorem fold2:
  "(fold2 s1 s2) (ctor2 x) = s2 (F2map id (fold1 s1 s2) (fold2 s1 s2) x)"
  apply (rule morE2)
   apply (rule mor_fold)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule subset_UNIV)
  done

lemma mor_UNIV: "mor UNIV UNIV s1 s2 UNIV UNIV s1' s2' f g \<longleftrightarrow>
   f o s1 = s1' o F1map id f g \<and> g o s2 = s2' o F2map id f g"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule ext)
    apply (rule trans)
     apply (rule o_apply)
    apply (rule trans)
     apply (erule morE1)
     apply (rule CollectI)
     apply (rule conjI)
      apply (rule subset_UNIV)
     apply (rule conjI)
      apply (rule subset_UNIV)
     apply (rule subset_UNIV)
    apply (rule sym[OF o_apply])

   apply (rule ext)
   apply (rule trans)
    apply (rule o_apply)
   apply (rule trans)
    apply (erule morE2)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule subset_UNIV)
    apply (rule conjI)
     apply (rule subset_UNIV)
    apply (rule subset_UNIV)
   apply (rule sym[OF o_apply])

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
   apply (rule UNIV_I)
  apply (erule conjE)
  apply (drule iffD1[OF fun_eq_iff])
  apply (drule iffD1[OF fun_eq_iff])
  apply (rule conjI)
   apply (rule ballI)
   apply (erule allE)+
   apply (rule trans)
    apply (erule trans[OF sym[OF o_apply]])
   apply (rule o_apply)
  apply (rule ballI)
  apply (erule allE)+
  apply (rule trans)
   apply (erule trans[OF sym[OF o_apply]])
  apply (rule o_apply)
  done

lemma fold_unique_mor: "mor UNIV UNIV ctor1 ctor2 UNIV UNIV s1 s2 f g \<Longrightarrow>
  f = fold1 s1 s2 \<and> g = fold2 s1 s2"
  apply (rule conjI)
   apply (rule surj_fun_eq)
    apply (rule type_definition.Abs_image[OF type_definition_IF1])
   apply (rule ballI)
   apply (rule conjunct1)
   apply (rule init_unique_mor)
      apply assumption
     apply (rule Rep_IF2)
    apply (rule mor_comp)
     apply (rule mor_Abs_IF)
    apply assumption
   apply (rule mor_comp)
    apply (rule mor_Abs_IF)
   apply (rule mor_fold)

  apply (rule surj_fun_eq)
   apply (rule type_definition.Abs_image[OF type_definition_IF2])
  apply (rule ballI)
  apply (rule conjunct2)
  apply (rule init_unique_mor)
     apply (rule Rep_IF1)
    apply assumption
   apply (rule mor_comp)
    apply (rule mor_Abs_IF)
   apply assumption
  apply (rule mor_comp)
   apply (rule mor_Abs_IF)
  apply (rule mor_fold)
  done

lemmas fold_unique = fold_unique_mor[OF iffD2[OF mor_UNIV], OF conjI]

lemmas fold1_ctor = sym[OF conjunct1[OF fold_unique_mor[OF mor_incl[OF subset_UNIV subset_UNIV]]]]
lemmas fold2_ctor = sym[OF conjunct2[OF fold_unique_mor[OF mor_incl[OF subset_UNIV subset_UNIV]]]]

text \<open>Case distinction\<close>

lemmas ctor1_o_fold1 =
  trans[OF conjunct1[OF fold_unique_mor[OF mor_comp[OF mor_fold mor_str]]] fold1_ctor]
lemmas ctor2_o_fold2 =
  trans[OF conjunct2[OF fold_unique_mor[OF mor_comp[OF mor_fold mor_str]]] fold2_ctor]

(* unfold *)
definition "dtor1 = fold1 (F1map id ctor1 ctor2) (F2map id ctor1 ctor2)"
definition "dtor2 = fold2 (F1map id ctor1 ctor2) (F2map id ctor1 ctor2)"

ML \<open>Local_Defs.fold @{context} @{thms dtor1_def} @{thm ctor1_o_fold1}\<close>
ML \<open>Local_Defs.fold @{context} @{thms dtor2_def} @{thm ctor2_o_fold2}\<close>

lemma ctor1_o_dtor1: "ctor1 o dtor1 = id"
  unfolding dtor1_def
  apply (rule ctor1_o_fold1)
  done

lemma ctor2_o_dtor2: "ctor2 o dtor2 = id"
  unfolding dtor2_def
  apply (rule ctor2_o_fold2)
  done
lemma dtor1_o_ctor1: "dtor1 o ctor1 = id"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fun_cong[OF dtor1_def]])
  apply (rule trans[OF fold1])
  apply (rule trans[OF F1map_comp_id])
  apply (rule trans[OF F1map_congL])
    apply (rule ballI)
    apply (rule trans[OF fun_cong[OF ctor1_o_fold1] id_apply])
   apply (rule ballI)
   apply (rule trans[OF fun_cong[OF ctor2_o_fold2] id_apply])
  apply (rule sym[OF id_apply])
  done

lemma dtor2_o_ctor2: "dtor2 o ctor2 = id"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fun_cong[OF dtor2_def]])
  apply (rule trans[OF fold2])
  apply (rule trans[OF F2map_comp_id])
  apply (rule trans[OF F2map_congL])
    apply (rule ballI)
    apply (rule trans[OF fun_cong[OF ctor1_o_fold1] id_apply])
   apply (rule ballI)
   apply (rule trans[OF fun_cong[OF ctor2_o_fold2] id_apply])
  apply (rule sym[OF id_apply])
  done

lemmas dtor1_ctor1 = pointfree_idE[OF dtor1_o_ctor1]
lemmas dtor2_ctor2 = pointfree_idE[OF dtor2_o_ctor2]
lemmas ctor1_dtor1 = pointfree_idE[OF ctor1_o_dtor1]
lemmas ctor2_dtor2 = pointfree_idE[OF ctor2_o_dtor2]

lemmas bij_dtor1 = o_bij[OF ctor1_o_dtor1 dtor1_o_ctor1]
lemmas inj_dtor1 = bij_is_inj[OF bij_dtor1]
lemmas surj_dtor1 = bij_is_surj[OF bij_dtor1]
lemmas dtor1_nchotomy = surjD[OF surj_dtor1]
lemmas dtor1_diff = inj_eq[OF inj_dtor1]
lemmas dtor1_cases = exE[OF dtor1_nchotomy]
lemmas bij_dtor2 = o_bij[OF ctor2_o_dtor2 dtor2_o_ctor2]
lemmas inj_dtor2 = bij_is_inj[OF bij_dtor2]
lemmas surj_dtor2 = bij_is_surj[OF bij_dtor2]
lemmas dtor2_nchotomy = surjD[OF surj_dtor2]
lemmas dtor2_diff = inj_eq[OF inj_dtor2]
lemmas dtor2_cases = exE[OF dtor2_nchotomy]

lemmas bij_ctor1 = o_bij[OF dtor1_o_ctor1 ctor1_o_dtor1]
lemmas inj_ctor1 = bij_is_inj[OF bij_ctor1]
lemmas surj_ctor1 = bij_is_surj[OF bij_ctor1]
lemmas ctor1_nchotomy = surjD[OF surj_ctor1]
lemmas ctor1_diff = inj_eq[OF inj_ctor1]
lemmas ctor1_cases = exE[OF ctor1_nchotomy]
lemmas bij_ctor2 = o_bij[OF dtor2_o_ctor2 ctor2_o_dtor2]
lemmas inj_ctor2 = bij_is_inj[OF bij_ctor2]
lemmas surj_ctor2 = bij_is_surj[OF bij_ctor2]
lemmas ctor2_nchotomy = surjD[OF surj_ctor2]
lemmas ctor2_diff = inj_eq[OF inj_ctor2]
lemmas ctor2_cases = exE[OF ctor2_nchotomy]

text \<open>Primitive recursion\<close>

definition rec1 where
  "rec1 s1 s2 = snd o fold1 (<ctor1 o F1map id fst fst, s1>) (<ctor2 o F2map id fst fst, s2>)"
definition rec2 where
  "rec2 s1 s2 = snd o fold2 (<ctor1 o F1map id fst fst, s1>) (<ctor2 o F2map id fst fst, s2>)"

lemma fold1_o_ctor1: "fold1 s1 s2 \<circ> ctor1 = s1 \<circ> F1map id (fold1 s1 s2) (fold2 s1 s2)"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm fold1}) 1\<close>)
lemma fold2_o_ctor2: "fold2 s1 s2 \<circ> ctor2 = s2 \<circ> F2map id (fold1 s1 s2) (fold2 s1 s2)"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm fold2}) 1\<close>)

lemmas fst_rec1_pair =
  trans[OF conjunct1[OF fold_unique[OF
        trans[OF o_assoc[symmetric] trans[OF arg_cong2[of _ _ _ _ "(o)", OF refl
              trans[OF fold1_o_ctor1 convol_o]]], OF trans[OF fst_convol]]
        trans[OF o_assoc[symmetric] trans[OF arg_cong2[of _ _ _ _ "(o)", OF refl
              trans[OF fold2_o_ctor2 convol_o]]], OF trans[OF fst_convol]]]]
    fold1_ctor, unfolded F1.map_comp0[of id, unfolded id_o] F2.map_comp0[of id, unfolded id_o] o_assoc,
    OF refl refl]
lemmas fst_rec2_pair =
  trans[OF conjunct2[OF fold_unique[OF
        trans[OF o_assoc[symmetric] trans[OF arg_cong2[of _ _ _ _ "(o)", OF refl
              trans[OF fold1_o_ctor1 convol_o]]], OF trans[OF fst_convol]]
        trans[OF o_assoc[symmetric] trans[OF arg_cong2[of _ _ _ _ "(o)", OF refl
              trans[OF fold2_o_ctor2 convol_o]]], OF trans[OF fst_convol]]]]
    fold2_ctor, unfolded F1.map_comp0[of id, unfolded id_o] F2.map_comp0[of id, unfolded id_o] o_assoc,
    OF refl refl]

theorem rec1: "rec1 s1 s2 (ctor1 x) = s1 (F1map id (<id, rec1 s1 s2>) (<id, rec2 s1 s2>) x)"
  unfolding rec1_def rec2_def o_apply fold1 snd_convol'
    convol_expand_snd[OF fst_rec1_pair] convol_expand_snd[OF fst_rec2_pair] ..

theorem rec2: "rec2 s1 s2 (ctor2 x) = s2 (F2map id (<id, rec1 s1 s2>) (<id, rec2 s1 s2>) x)"
  unfolding rec1_def rec2_def o_apply fold2 snd_convol'
    convol_expand_snd[OF fst_rec1_pair] convol_expand_snd[OF fst_rec2_pair] ..

lemma rec_unique:
  "f \<circ> ctor1 = s1 \<circ> F1map id <id , f> <id , g> \<Longrightarrow>
    g \<circ> ctor2 = s2 \<circ> F2map id <id , f> <id , g> \<Longrightarrow> f = rec1 s1 s2 \<and> g = rec2 s1 s2"
  unfolding rec1_def rec2_def convol_expand_snd'[OF fst_rec1_pair] convol_expand_snd'[OF fst_rec2_pair]
  apply (rule fold_unique)
   apply (unfold convol_o id_o o_id F1.map_comp0[symmetric] F2.map_comp0[symmetric]
      F1.map_id0 F2.map_id0 o_assoc[symmetric] fst_convol)
   apply (erule arg_cong2[of _ _ _ _ BNF_Def.convol, OF refl])
  apply (erule arg_cong2[of _ _ _ _ BNF_Def.convol, OF refl])
  done


text \<open>Induction\<close>

theorem ctor_induct:
  "\<lbrakk>\<And>x. (\<And>a. a \<in> F1set2 x \<Longrightarrow> phi1 a) \<Longrightarrow> (\<And>a. a \<in> F1set3 x \<Longrightarrow> phi2 a) \<Longrightarrow> phi1 (ctor1 x);
  \<And>x. (\<And>a. a \<in> F2set2 x \<Longrightarrow> phi1 a) \<Longrightarrow> (\<And>a. a \<in> F2set3 x \<Longrightarrow> phi2 a) \<Longrightarrow> phi2 (ctor2 x)\<rbrakk> \<Longrightarrow>
  phi1 a \<and> phi2 b"
  apply (rule mp)

   apply (rule impI)
   apply (erule conjE)
   apply (rule conjI)
    apply (rule iffD1[OF arg_cong[OF Rep_IF1_inverse]])
    apply (erule bspec[OF _ Rep_IF1])
   apply (rule iffD1[OF arg_cong[OF Rep_IF2_inverse]])
   apply (erule bspec[OF _ Rep_IF2])
  apply (rule init_induct)

  apply (rule conjI)

   apply (drule asm_rl)
   apply (erule thin_rl)
   apply (rule ballI)
   apply (rule impI)
   apply (rule iffD2[OF arg_cong[OF morE1[OF mor_Abs_IF]]])
    apply assumption
   apply (erule CollectE conjE)+
   apply (drule meta_spec)
   apply (drule meta_mp)
    apply (rule iffD1[OF arg_cong[OF Rep_IF1_inverse]])
    apply (erule bspec)
    apply (drule rev_subsetD)
     apply (rule equalityD1)
     apply (rule F1.set_map(2))
    apply (erule imageE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule ssubst_mem[OF Abs_IF1_inverse])
     apply (erule subsetD)
     apply assumption
    apply assumption

   apply (drule meta_mp)
    apply (rule iffD1[OF arg_cong[OF Rep_IF2_inverse]])
    apply (erule bspec)
    apply (drule rev_subsetD)
     apply (rule equalityD1)
     apply (rule F1.set_map(3))
    apply (erule imageE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule ssubst_mem[OF Abs_IF2_inverse])
     apply (erule subsetD)
     apply assumption
    apply assumption

   apply assumption

  apply (erule thin_rl)
  apply (drule asm_rl)
  apply (rule ballI)
  apply (rule impI)
  apply (rule iffD2[OF arg_cong[OF morE2[OF mor_Abs_IF]]])
   apply assumption
  apply (erule CollectE conjE)+
  apply (drule meta_spec)
  apply (drule meta_mp)
   apply (rule iffD1[OF arg_cong[OF Rep_IF1_inverse]])
   apply (erule bspec)
   apply (drule rev_subsetD)
    apply (rule equalityD1)
    apply (rule F2.set_map(2))
   apply (erule imageE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule ssubst_mem[OF Abs_IF1_inverse])
    apply (erule subsetD)
    apply assumption
   apply assumption

  apply (drule meta_mp)
   apply (rule iffD1[OF arg_cong[OF Rep_IF2_inverse]])
   apply (erule bspec)
   apply (drule rev_subsetD)
    apply (rule equalityD1)
    apply (rule F2.set_map(3))
   apply (erule imageE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule ssubst_mem[OF Abs_IF2_inverse])
    apply (erule subsetD)
    apply assumption
   apply assumption

  apply assumption
  done

theorem ctor_induct2:
  "\<lbrakk>\<And>x y. (\<And>a b. a \<in> F1set2 x \<Longrightarrow> b \<in> F1set2 y \<Longrightarrow> phi1 a b) \<Longrightarrow>
      (\<And>a b. a \<in> F1set3 x \<Longrightarrow> b \<in> F1set3 y \<Longrightarrow> phi2 a b) \<Longrightarrow> phi1 (ctor1 x) (ctor1 y);
    \<And>x y. (\<And>a b. a \<in> F2set2 x \<Longrightarrow> b \<in> F2set2 y \<Longrightarrow> phi1 a b) \<Longrightarrow>
      (\<And>a b. a \<in> F2set3 x \<Longrightarrow> b \<in> F2set3 y \<Longrightarrow> phi2 a b) \<Longrightarrow> phi2 (ctor2 x) (ctor2 y)\<rbrakk> \<Longrightarrow>
   phi1 a1 b1 \<and> phi2 a2 b2"
  apply (rule rev_mp)
   apply (rule ctor_induct[of "%a1. (\<forall>x. phi1 a1 x)" "%a2. (\<forall>y. phi2 a2 y)" a1 a2])
    apply (rule allI[OF conjunct1[OF ctor_induct[OF asm_rl TrueI]]])
    apply (drule meta_spec2)
    apply (erule thin_rl)
    apply (tactic \<open>(dtac @{context} @{thm meta_mp} THEN_ALL_NEW Goal.norm_hhf_tac @{context}) 1\<close>)
     apply (drule meta_spec)+
     apply (erule meta_mp[OF spec])
     apply assumption
    apply (drule meta_mp)
     apply (drule meta_spec)+
     apply (erule meta_mp[OF spec])
     apply assumption
    apply assumption

   apply (rule allI[OF conjunct2[OF ctor_induct[OF TrueI asm_rl]]])
   apply (erule thin_rl)
   apply (drule meta_spec2)
   apply (drule meta_mp)
    apply (drule meta_spec)+
    apply (erule meta_mp[OF spec])
    apply assumption
   apply (erule meta_mp)
   apply (drule meta_spec)+
   apply (erule meta_mp[OF spec])
   apply assumption

  apply (rule impI)
  apply (erule conjE allE)+
  apply (rule conjI)
   apply assumption
  apply assumption
  done


subsection \<open>The Result as an BNF\<close>

text\<open>The map operator\<close>

abbreviation IF1map where "IF1map f \<equiv> fold1 (ctor1 o (F1map f id id)) (ctor2 o (F2map f id id))"
abbreviation IF2map where "IF2map f \<equiv> fold2 (ctor1 o (F1map f id id)) (ctor2 o (F2map f id id))"

theorem IF1map:
  "(IF1map f) o ctor1 = ctor1 o (F1map f (IF1map f) (IF2map f))"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold1])
  apply (rule trans[OF o_apply])
  apply (rule trans[OF arg_cong[OF F1map_comp_id]])
  apply (rule trans[OF arg_cong[OF F1.map_cong0]])
     apply (rule refl)
    apply (rule trans[OF o_apply])
    apply (rule id_apply)
   apply (rule trans[OF o_apply])
   apply (rule id_apply)
  apply (rule sym[OF o_apply])
  done

theorem IF2map:
  "(IF2map f) o ctor2 = ctor2 o (F2map f (IF1map f) (IF2map f))"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold2])
  apply (rule trans[OF o_apply])
  apply (rule trans[OF arg_cong[OF F2map_comp_id]])
  apply (rule trans[OF arg_cong[OF F2.map_cong0]])
     apply (rule refl)
    apply (rule trans[OF o_apply])
    apply (rule id_apply)
   apply (rule trans[OF o_apply])
   apply (rule id_apply)
  apply (rule sym[OF o_apply])
  done

lemmas IF1map_simps = o_eq_dest[OF IF1map]
lemmas IF2map_simps = o_eq_dest[OF IF2map]

lemma IFmap_unique:
  "\<lbrakk>u o ctor1 = ctor1 o F1map f u v; v o ctor2 = ctor2 o F2map f u v\<rbrakk> \<Longrightarrow>
    u = IF1map f \<and> v = IF2map f"
  apply (rule fold_unique)
  unfolding o_assoc[symmetric] F1.map_comp0[symmetric] F2.map_comp0[symmetric] id_o o_id
   apply assumption
  apply assumption
  done

theorem IF1map_id: "IF1map id = id"
  apply (rule sym)
  apply (rule conjunct1[OF IFmap_unique])
   apply (rule trans[OF id_o])
   apply (rule trans[OF sym[OF o_id]])
   apply (rule arg_cong[OF sym[OF F1.map_id0]])
  apply (rule trans[OF id_o])
  apply (rule trans[OF sym[OF o_id]])
  apply (rule arg_cong[OF sym[OF F2.map_id0]])
  done

theorem IF2map_id: "IF2map id = id"
  apply (rule sym)
  apply (rule conjunct2[OF IFmap_unique])
   apply (rule trans[OF id_o])
   apply (rule trans[OF sym[OF o_id]])
   apply (rule arg_cong[OF sym[OF F1.map_id0]])
  apply (rule trans[OF id_o])
  apply (rule trans[OF sym[OF o_id]])
  apply (rule arg_cong[OF sym[OF F2.map_id0]])
  done

theorem IF1map_comp: "IF1map (g o f) = IF1map g o IF1map f"
  apply (rule sym)
  apply (rule conjunct1[OF IFmap_unique])
   apply (rule ext)
   apply (rule trans[OF o_apply])
   apply (rule trans[OF o_apply])
   apply (rule trans[OF arg_cong[OF IF1map_simps]])
   apply (rule trans[OF IF1map_simps])
   apply (rule trans[OF arg_cong[OF F1.map_comp]])
   apply (rule sym[OF o_apply])
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF o_apply])
  apply (rule trans[OF arg_cong[OF IF2map_simps]])
  apply (rule trans[OF IF2map_simps])
  apply (rule trans[OF arg_cong[OF F2.map_comp]])
  apply (rule sym[OF o_apply])
  done

theorem IF2map_comp: "IF2map (g o f) = IF2map g o IF2map f"
  apply (rule sym)
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm conjunct2[OF IFmap_unique]}) 1\<close>)
   apply (rule ext)
   apply (rule trans[OF o_apply])
   apply (rule trans[OF o_apply])
   apply (rule trans[OF arg_cong[OF IF2map_simps]])
   apply (rule trans[OF IF2map_simps])
   apply (rule trans[OF arg_cong[OF F2.map_comp]])
   apply (rule sym[OF o_apply])
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF o_apply])
  apply (rule trans[OF arg_cong[OF IF1map_simps]])
  apply (rule trans[OF IF1map_simps])
  apply (rule trans[OF arg_cong[OF F1.map_comp]])
  apply (rule sym[OF o_apply])
  done


text\<open>The bound\<close>

abbreviation IFbd where "IFbd \<equiv> bd_F1 +c bd_F2"

theorem IFbd_card_order: "card_order IFbd"
  apply (rule card_order_csum)
   apply (rule F1.bd_card_order)
  apply (rule F2.bd_card_order)
  done

lemma IFbd_Cinfinite: "Cinfinite IFbd"
  apply (rule Cinfinite_csum1)
  apply (rule F1.bd_Cinfinite)
  done

lemmas IFbd_cinfinite = conjunct1[OF IFbd_Cinfinite]


text \<open>The set operator\<close>

(* "IFcol" stands for "collect"  *)

abbreviation IF1col where "IF1col \<equiv> (\<lambda>X. F1set1 X \<union> (\<Union>(F1set2 X) \<union> \<Union>(F1set3 X)))"
abbreviation IF2col where "IF2col \<equiv> (\<lambda>X. F2set1 X \<union> (\<Union>(F2set2 X) \<union> \<Union>(F2set3 X)))"

abbreviation IF1set where "IF1set \<equiv> fold1 IF1col IF2col"
abbreviation IF2set where "IF2set \<equiv> fold2 IF1col IF2col"

abbreviation IF1in where "IF1in A \<equiv> {x. IF1set x \<subseteq> A}"
abbreviation IF2in where "IF2in A \<equiv> {x. IF2set x \<subseteq> A}"

lemma IF1set: "IF1set o ctor1 = IF1col o (F1map id IF1set IF2set)"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold1])
  apply (rule sym[OF o_apply])
  done

lemma IF2set: "IF2set o ctor2 = IF2col o (F2map id IF1set IF2set)"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold2])
  apply (rule sym[OF o_apply])
  done

theorem IF1set_simps:
  "IF1set (ctor1 x) = F1set1 x \<union> ((\<Union>a \<in> F1set2 x. IF1set a) \<union> (\<Union>a \<in> F1set3 x. IF2set a))"
  apply (rule trans[OF o_eq_dest[OF IF1set]])
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule trans[OF F1.set_map(1) trans[OF fun_cong[OF image_id] id_apply]])
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule arg_cong[OF F1.set_map(2)])
  apply (rule arg_cong[OF F1.set_map(3)])
  done

theorem IF2set_simps:
  "IF2set (ctor2 x) = F2set1 x \<union> ((\<Union>a \<in> F2set2 x. IF1set a) \<union> (\<Union>a \<in> F2set3 x. IF2set a))"
  apply (rule trans[OF o_eq_dest[OF IF2set]])
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule trans[OF F2.set_map(1) trans[OF fun_cong[OF image_id] id_apply]])
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule arg_cong[OF F2.set_map(2)])
  apply (rule arg_cong[OF F2.set_map(3)])
  done

lemmas F1set1_IF1set = xt1(3)[OF IF1set_simps Un_upper1]
lemmas F1set2_IF1set = subset_trans[OF UN_upper subset_trans[OF Un_upper1 xt1(3)[OF IF1set_simps Un_upper2]]]
lemmas F1set3_IF1set = subset_trans[OF UN_upper subset_trans[OF Un_upper2 xt1(3)[OF IF1set_simps Un_upper2]]]

lemmas F2set1_IF2set = xt1(3)[OF IF2set_simps Un_upper1]
lemmas F2set2_IF2set = subset_trans[OF UN_upper subset_trans[OF Un_upper1 xt1(3)[OF IF2set_simps Un_upper2]]]
lemmas F2set3_IF2set = subset_trans[OF UN_upper subset_trans[OF Un_upper2 xt1(3)[OF IF2set_simps Un_upper2]]]

text \<open>The BNF conditions for IF\<close>

lemma IFset_natural:
  "f ` (IF1set x) = IF1set (IF1map f x) \<and> f ` (IF2set y) = IF2set (IF2map f y)"
  apply (rule ctor_induct[of _ _ x y])

   apply (rule trans)
    apply (rule image_cong)
     apply (rule IF1set_simps)
    apply (rule refl)
   apply (rule sym)
   apply (rule trans[OF arg_cong[of _ _ IF1set, OF IF1map_simps] trans[OF IF1set_simps]])

   apply (rule sym)
   apply (rule trans)
    apply (rule image_Un)
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule sym)
    apply (rule F1.set_map(1))

   apply (rule trans)
    apply (rule image_Un)
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule trans)
     apply (rule image_UN)
    apply (rule trans)
     apply (rule SUP_cong)
      apply (rule refl)
     apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
    apply (rule sym)
    apply (rule trans)
     apply (rule SUP_cong)
      apply (rule F1.set_map(2))
     apply (rule refl)
    apply (rule UN_simps(10))

   apply (rule trans)
    apply (rule image_UN)
   apply (rule trans)
    apply (rule SUP_cong)
     apply (rule refl)
    apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
   apply (rule sym)
   apply (rule trans)
    apply (rule SUP_cong)
     apply (rule F1.set_map(3))
    apply (rule refl)
   apply (rule UN_simps(10))


  apply (rule trans)
   apply (rule image_cong)
    apply (rule IF2set_simps)
   apply (rule refl)
  apply (rule sym)
  apply (rule trans[OF arg_cong[of _ _ IF2set, OF IF2map_simps] trans[OF IF2set_simps]])

  apply (rule sym)
  apply (rule trans)
   apply (rule image_Un)
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule sym)
   apply (rule F2.set_map(1))

  apply (rule trans)
   apply (rule image_Un)
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])

   apply (rule trans)
    apply (rule image_UN)
   apply (rule trans)
    apply (rule SUP_cong)
     apply (rule refl)
    apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
   apply (rule sym)
   apply (rule trans)
    apply (rule SUP_cong)
     apply (rule F2.set_map(2))
    apply (rule refl)
   apply (rule UN_simps(10))

  apply (rule trans)
   apply (rule image_UN)
  apply (rule trans)
   apply (rule SUP_cong)
    apply (rule refl)
   apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
  apply (rule sym)
  apply (rule trans)
   apply (rule SUP_cong)
    apply (rule F2.set_map(3))
   apply (rule refl)
  apply (rule UN_simps(10))
  done

theorem IF1set_natural: "IF1set o (IF1map f) = image f o IF1set"
  apply (rule ext)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule sym)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule conjunct1)
  apply (rule IFset_natural)
  done

theorem IF2set_natural: "IF2set o (IF2map f) = image f o IF2set"
  apply (rule ext)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule sym)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule conjunct2)
  apply (rule IFset_natural)
  done

lemma IFmap_cong:
  "((\<forall>a \<in> IF1set x. f a = g a) \<longrightarrow> IF1map f x = IF1map g x) \<and>
   ((\<forall>a \<in> IF2set y. f a = g a) \<longrightarrow> IF2map f y = IF2map g y)"
  apply (rule ctor_induct[of _ _ x y])

   apply (rule impI)
   apply (rule trans)
    apply (rule IF1map_simps)
   apply (rule trans)
    apply (rule arg_cong[OF F1.map_cong0])
      apply (erule bspec)
      apply (erule rev_subsetD)
      apply (rule F1set1_IF1set)
     apply (rule mp)
      apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
     apply (rule ballI)
     apply (erule bspec)
     apply (erule rev_subsetD)
     apply (erule F1set2_IF1set)
    apply (rule mp)
     apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
    apply (rule ballI)
    apply (erule bspec)
    apply (erule rev_subsetD)
    apply (erule F1set3_IF1set)
   apply (rule sym)
   apply (rule IF1map_simps)

  apply (rule impI)
  apply (rule trans)
   apply (rule IF2map_simps)
  apply (rule trans)
   apply (rule arg_cong[OF F2.map_cong0])
     apply (erule bspec)
     apply (erule rev_subsetD)
     apply (rule F2set1_IF2set)
    apply (rule mp)
     apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
    apply (rule ballI)
    apply (erule bspec)
    apply (erule rev_subsetD)
    apply (erule F2set2_IF2set)
   apply (rule mp)
    apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
   apply (rule ballI)
   apply (erule bspec)
   apply (erule rev_subsetD)
   apply (erule F2set3_IF2set)
  apply (rule sym)
  apply (rule IF2map_simps)
  done

theorem IF1map_cong:
  "(\<And>a. a \<in> IF1set x \<Longrightarrow> f a = g a) \<Longrightarrow> IF1map f x = IF1map g x"
  apply (rule mp)
   apply (rule conjunct1)
   apply (rule IFmap_cong)
  apply (rule ballI)
  apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
  done

theorem IF2map_cong:
  "(\<And>a. a \<in> IF2set x \<Longrightarrow> f a = g a) \<Longrightarrow> IF2map f x = IF2map g x"
  apply (rule mp)
   apply (rule conjunct2)
   apply (rule IFmap_cong)
  apply (rule ballI)
  apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
  done

lemma IFset_bd:
  "|IF1set (x :: 'a IF1)| \<le>o IFbd \<and> |IF2set (y :: 'a IF2)| \<le>o IFbd"
  apply (rule ctor_induct[of _ _ x y])

   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule IF1set_simps)
   apply (rule Un_Cinfinite_bound)
     apply (rule F1set1_bd)
    apply (rule Un_Cinfinite_bound)
      apply (rule UNION_Cinfinite_bound)
        apply (rule F1set2_bd)
       apply (rule ballI)
       apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
      apply (rule IFbd_Cinfinite)
     apply (rule UNION_Cinfinite_bound)
       apply (rule F1set3_bd)
      apply (rule ballI)
      apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
     apply (rule IFbd_Cinfinite)
    apply (rule IFbd_Cinfinite)
   apply (rule IFbd_Cinfinite)

  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst)
   apply (rule IF2set_simps)
  apply (rule Un_Cinfinite_bound)
    apply (rule F2set1_bd)
   apply (rule Un_Cinfinite_bound)
     apply (rule UNION_Cinfinite_bound)
       apply (rule F2set2_bd)
      apply (rule ballI)
      apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
     apply (rule IFbd_Cinfinite)
    apply (rule UNION_Cinfinite_bound)
      apply (rule F2set3_bd)
     apply (rule ballI)
     apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
    apply (rule IFbd_Cinfinite)
   apply (rule IFbd_Cinfinite)
  apply (rule IFbd_Cinfinite)
  done

lemmas IF1set_bd = conjunct1[OF IFset_bd]
lemmas IF2set_bd = conjunct2[OF IFset_bd]

definition IF1rel where
  "IF1rel R =
     (BNF_Def.Grp (IF1in (Collect (case_prod R))) (IF1map fst))^--1 OO
     (BNF_Def.Grp (IF1in (Collect (case_prod R))) (IF1map snd))"

definition IF2rel where
  "IF2rel R =
     (BNF_Def.Grp (IF2in (Collect (case_prod R))) (IF2map fst))^--1 OO
     (BNF_Def.Grp (IF2in (Collect (case_prod R))) (IF2map snd))"

lemma in_IF1rel:
  "IF1rel R x y \<longleftrightarrow> (\<exists> z. z \<in> IF1in (Collect (case_prod R)) \<and> IF1map fst z = x \<and> IF1map snd z = y)"
  unfolding IF1rel_def by (rule predicate2_eqD[OF OO_Grp_alt])

lemma in_IF2rel:
  "IF2rel R x y \<longleftrightarrow> (\<exists> z. z \<in> IF2in (Collect (case_prod R)) \<and> IF2map fst z = x \<and> IF2map snd z = y)"
  unfolding IF2rel_def by (rule predicate2_eqD[OF OO_Grp_alt])

lemma IF1rel_F1rel: "IF1rel R (ctor1 a) (ctor1 b) \<longleftrightarrow> F1rel R (IF1rel R) (IF2rel R) a b"
  apply (rule iffI)
   apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)+
   apply (erule exE conjE CollectE)+
   apply (rule iffD2)
    apply (rule F1.in_rel)
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (rule subset_trans)
      apply (rule F1set1_IF1set)
     apply (erule ord_eq_le_trans[OF arg_cong[OF ctor1_dtor1]])

    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule iffD2)
      apply (rule in_IF1rel)
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (erule subset_trans[OF F1set2_IF1set])
      apply (erule ord_eq_le_trans[OF arg_cong[OF ctor1_dtor1]])
     apply (rule conjI)
      apply (rule refl)
     apply (rule refl)

    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(3))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule iffD2)
     apply (rule in_IF2rel)
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (rule subset_trans)
      apply (rule F1set3_IF1set)
      apply assumption
     apply (erule ord_eq_le_trans[OF arg_cong[OF ctor1_dtor1]])
    apply (rule conjI)
     apply (rule refl)
    apply (rule refl)
   apply (rule conjI)

    apply (rule trans)
     apply (rule F1.map_comp)
    apply (rule trans)
     apply (rule F1.map_cong0)
       apply (rule fun_cong[OF o_id])
      apply (rule trans)
       apply (rule o_apply)
      apply (rule fst_conv)
     apply (rule trans)
      apply (rule o_apply)
     apply (rule fst_conv)
    apply (rule iffD1[OF ctor1_diff])
    apply (rule trans)
     apply (rule sym)
     apply (rule IF1map_simps)
    apply (erule trans[OF arg_cong[OF ctor1_dtor1]])


   apply (rule trans)
    apply (rule F1.map_comp)
   apply (rule trans)
    apply (rule F1.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans)
      apply (rule o_apply)
     apply (rule snd_conv)
    apply (rule trans)
     apply (rule o_apply)
    apply (rule snd_conv)
   apply (rule iffD1[OF ctor1_diff])
   apply (rule trans)
    apply (rule sym)
    apply (rule IF1map_simps)
   apply (erule trans[OF arg_cong[OF ctor1_dtor1]])

  apply (tactic \<open>dtac @{context} (@{thm F1.in_rel[THEN iffD1]}) 1\<close>)
  apply (erule exE conjE CollectE)+
  apply (rule iffD2)
   apply (rule in_IF1rel)
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule IF1set_simps)
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule box_equals[OF _ refl])
      apply (rule F1.set_map(1))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule SUP_cong[OF _ refl])
     apply (rule F1.set_map(2))
    apply (rule UN_least)
    apply (drule rev_subsetD)
     apply (erule image_mono)
    apply (erule imageE)
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply (erule CollectD)

   apply (rule ord_eq_le_trans)
    apply (rule SUP_cong[OF _ refl])
    apply (rule F1.set_map(3))
   apply (rule UN_least)
   apply (drule rev_subsetD)
    apply (erule image_mono)
   apply (erule imageE)
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
   apply (drule someI_ex)
   apply (erule conjE)+
   apply (erule CollectD)

  apply (rule conjI)
   apply (rule trans)
    apply (rule IF1map_simps)
   apply (rule iffD2[OF ctor1_diff])
   apply (rule trans)
    apply (rule F1.map_comp)
   apply (rule trans)
    apply (rule F1.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans[OF o_apply])
     apply (drule rev_subsetD)
      apply assumption
     apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
     apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
     apply hypsubst
     apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
     apply (drule someI_ex)
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply assumption

  apply (rule trans)
   apply (rule IF1map_simps)
  apply (rule iffD2[OF ctor1_diff])
  apply (rule trans)
   apply (rule F1.map_comp)
  apply (rule trans)
   apply (rule F1.map_cong0)
     apply (rule fun_cong[OF o_id])
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply (rule trans[OF o_apply])
   apply (drule rev_subsetD)
    apply assumption
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
   apply (drule someI_ex)
   apply (erule conjE)+
   apply assumption
  apply assumption
  done

lemma IF2rel_F2rel: "IF2rel R (ctor2 a) (ctor2 b) \<longleftrightarrow> F2rel R (IF1rel R) (IF2rel R) a b"
  apply (rule iffI)
   apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)+
   apply (erule exE conjE CollectE)+
   apply (rule iffD2)
    apply (rule F2.in_rel)
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F2.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (rule subset_trans)
      apply (rule F2set1_IF2set)
     apply (erule ord_eq_le_trans[OF arg_cong[OF ctor2_dtor2]])

    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F2.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule iffD2)
      apply (rule in_IF1rel)
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (rule subset_trans)
       apply (rule F2set2_IF2set)
       apply assumption
      apply (erule ord_eq_le_trans[OF arg_cong[OF ctor2_dtor2]])
     apply (rule conjI)
      apply (rule refl)
     apply (rule refl)

    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(3))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule iffD2)
     apply (rule in_IF2rel)
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (rule subset_trans)
      apply (rule F2set3_IF2set)
      apply assumption
     apply (erule ord_eq_le_trans[OF arg_cong[OF ctor2_dtor2]])
    apply (rule conjI)
     apply (rule refl)
    apply (rule refl)
   apply (rule conjI)

    apply (rule trans)
     apply (rule F2.map_comp)
    apply (rule trans)
     apply (rule F2.map_cong0)
       apply (rule fun_cong[OF o_id])
      apply (rule trans)
       apply (rule o_apply)
      apply (rule fst_conv)
     apply (rule trans)
      apply (rule o_apply)
     apply (rule fst_conv)
    apply (rule iffD1[OF ctor2_diff])
    apply (rule trans)
     apply (rule sym)
     apply (rule IF2map_simps)
    apply (erule trans[OF arg_cong[OF ctor2_dtor2]])


   apply (rule trans)
    apply (rule F2.map_comp)
   apply (rule trans)
    apply (rule F2.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans)
      apply (rule o_apply)
     apply (rule snd_conv)
    apply (rule trans)
     apply (rule o_apply)
    apply (rule snd_conv)
   apply (rule iffD1[OF ctor2_diff])
   apply (rule trans)
    apply (rule sym)
    apply (rule IF2map_simps)
   apply (erule trans[OF arg_cong[OF ctor2_dtor2]])

  apply (tactic \<open>dtac @{context} (@{thm F2.in_rel[THEN iffD1]}) 1\<close>)
  apply (erule exE conjE CollectE)+
  apply (rule iffD2)
   apply (rule in_IF2rel)
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule IF2set_simps)
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule trans)
      apply (rule trans)
       apply (rule arg_cong[OF dtor2_ctor2])
      apply (rule F2.set_map(1))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule trans[OF arg_cong[OF dtor2_ctor2]])
     apply (rule arg_cong[OF F2.set_map(2)])
    apply (rule UN_least)
    apply (drule rev_subsetD)
     apply (erule image_mono)
    apply (erule imageE)
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply (erule CollectD)

   apply (rule ord_eq_le_trans)
    apply (rule trans[OF arg_cong[OF dtor2_ctor2]])
    apply (rule arg_cong[OF F2.set_map(3)])
   apply (rule UN_least)
   apply (drule rev_subsetD)
    apply (erule image_mono)
   apply (erule imageE)
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
   apply (drule someI_ex)
   apply (erule exE conjE)+
   apply (erule CollectD)

  apply (rule conjI)
   apply (rule trans)
    apply (rule arg_cong[OF dtor2_ctor2])
   apply (rule trans)
    apply (rule IF2map_simps)
   apply (rule iffD2)
    apply (rule ctor2_diff)
   apply (rule trans)
    apply (rule F2.map_comp)
   apply (rule trans)
    apply (rule F2.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans[OF o_apply])
     apply (drule rev_subsetD)
      apply assumption
     apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
     apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
     apply hypsubst
     apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
     apply (drule someI_ex)
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply assumption

  apply (rule trans)
   apply (rule arg_cong[OF dtor2_ctor2])
  apply (rule trans)
   apply (rule IF2map_simps)
  apply (rule iffD2)
   apply (rule ctor2_diff)
  apply (rule trans)
   apply (rule F2.map_comp)
  apply (rule trans)
   apply (rule F2.map_cong0)
     apply (rule fun_cong[OF o_id])
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IF1rel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply (rule trans[OF o_apply])
   apply (drule rev_subsetD)
    apply assumption
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (tactic \<open>dtac @{context} (@{thm in_IF2rel[THEN iffD1]}) 1\<close>)
   apply (drule someI_ex)
   apply (erule conjE)+
   apply assumption
  apply assumption
  done

lemma Irel_induct:
  assumes IH1: "\<forall>x y. F1rel P1 P2 P3 x y \<longrightarrow> P2 (ctor1 x) (ctor1 y)"
    and     IH2: "\<forall>x y. F2rel P1 P2 P3 x y \<longrightarrow> P3 (ctor2 x) (ctor2 y)"
  shows   "IF1rel P1 \<le> P2 \<and> IF2rel P1 \<le> P3"
  unfolding le_fun_def le_bool_def all_simps(1,2)[symmetric]
  apply (rule allI)+
  apply (rule ctor_induct2)
   apply (rule impI)
   apply (drule iffD1[OF IF1rel_F1rel])
   apply (rule mp[OF spec2[OF IH1]])
   apply (erule F1.rel_mono_strong0)
     apply (rule ballI[OF ballI[OF imp_refl]])
    apply (drule asm_rl)
    apply (erule thin_rl)
    apply (rule ballI[OF ballI])
    apply assumption
   apply (erule thin_rl)
   apply (drule asm_rl)
   apply (rule ballI[OF ballI])
   apply assumption

  apply (rule impI)
  apply (drule iffD1[OF IF2rel_F2rel])
  apply (rule mp[OF spec2[OF IH2]])
  apply (erule F2.rel_mono_strong0)
    apply (rule ballI[OF ballI[OF imp_refl]])
   apply (drule asm_rl)
   apply (erule thin_rl)
   apply (rule ballI[OF ballI])
   apply assumption
  apply (erule thin_rl)
  apply (drule asm_rl)
  apply (rule ballI[OF ballI])
  apply assumption
  done

lemma le_IFrel_Comp:
  "((IF1rel R OO IF1rel S) x1 y1 \<longrightarrow> IF1rel (R OO S) x1 y1) \<and>
       ((IF2rel R OO IF2rel S) x2 y2 \<longrightarrow> IF2rel (R OO S) x2 y2)"
  apply (rule ctor_induct2[of _ _ x1 y1 x2 y2])
   apply (rule impI)
   apply (erule nchotomy_relcomppE[OF ctor1_nchotomy])
   apply (drule iffD1[OF IF1rel_F1rel])
   apply (drule iffD1[OF IF1rel_F1rel])
   apply (rule iffD2[OF IF1rel_F1rel])
   apply (rule F1.rel_mono_strong0)
      apply (rule iffD2[OF predicate2_eqD[OF F1.rel_compp]])
      apply (rule relcomppI)
       apply assumption
      apply assumption
     apply (rule ballI impI)+
     apply assumption
    apply (rule ballI)+
    apply assumption
   apply (rule ballI)+
   apply assumption

  apply (rule impI)
  apply (erule nchotomy_relcomppE[OF ctor2_nchotomy])
  apply (drule iffD1[OF IF2rel_F2rel])
  apply (drule iffD1[OF IF2rel_F2rel])
  apply (rule iffD2[OF IF2rel_F2rel])
  apply (rule F2.rel_mono_strong0)
     apply (rule iffD2[OF predicate2_eqD[OF F2.rel_compp]])
     apply (rule relcomppI)
      apply assumption
     apply assumption
    apply (rule ballI impI)+
    apply assumption
   apply (rule ballI)+
   apply assumption
  apply (rule ballI)+
  apply assumption
  done

lemma le_IF1rel_Comp: "IF1rel R1 OO IF1rel R2 \<le> IF1rel (R1 OO R2)"
  by (rule predicate2I) (erule mp[OF conjunct1[OF le_IFrel_Comp]])

lemma le_IF2rel_Comp: "IF2rel R1 OO IF2rel R2 \<le> IF2rel (R1 OO R2)"
  by (rule predicate2I) (erule mp[OF conjunct2[OF le_IFrel_Comp]])

context includes lifting_syntax
begin

lemma fold_transfer:
  "((F1rel R S T ===> S) ===> (F2rel R S T ===> T) ===> IF1rel R ===> S) fold1 fold1 \<and>
  ((F1rel R S T ===> S) ===> (F2rel R S T ===> T) ===> IF2rel R ===> T) fold2 fold2"
  unfolding rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]
  unfolding rel_fun_iff_leq_vimage2p
  apply (rule allI impI)+
  apply (rule Irel_induct)
   apply (rule allI impI vimage2pI)+
   apply (unfold fold1 fold2) [1]
   apply (erule predicate2D_vimage2p)
   apply (rule rel_funD[OF rel_funD[OF rel_funD[OF rel_funD[OF F1.map_transfer]]]])
      apply (rule id_transfer)
     apply (rule vimage2p_rel_fun)
    apply (rule vimage2p_rel_fun)
   apply assumption


  apply (rule allI impI vimage2pI)+
  apply (unfold fold1 fold2) [1]
  apply (erule predicate2D_vimage2p)
  apply (rule rel_funD[OF rel_funD[OF rel_funD[OF rel_funD[OF F2.map_transfer]]]])
     apply (rule id_transfer)
    apply (rule vimage2p_rel_fun)
   apply (rule vimage2p_rel_fun)
  apply assumption
  done

end

definition "IF1wit x = ctor1 (wit2_F1 x (ctor2 wit_F2))"
definition "IF2wit = ctor2 wit_F2"

lemma IF1wit: "x \<in> IF1set (IF1wit y) \<Longrightarrow> x = y"
  unfolding IF1wit_def
  by (elim UnE F1.wit2[elim_format] F2.wit[elim_format] UN_E FalseE |
      rule refl |  hypsubst | assumption | unfold IF1set_simps IF2set_simps)+

lemma IF2wit: "x \<in> IF2set IF2wit \<Longrightarrow> False"
  unfolding IF2wit_def
  by (elim UnE F2.wit[elim_format] UN_E FalseE |
      rule refl |  hypsubst | assumption | unfold IF2set_simps)+

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Least_FP false 1 @{thm fold_unique}
    @{thms IF1map IF2map} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms fold1 fold2})
    @{thms F1.map_comp0[symmetric] F2.map_comp0[symmetric]} @{thms F1.map_cong0 F2.map_cong0}
\<close>

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Least_FP true 1 @{thm rec_unique}
    @{thms IF1map IF2map} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms rec1 rec2})
    @{thms F1.map_comp0[symmetric] F2.map_comp0[symmetric]} @{thms F1.map_cong0 F2.map_cong0}
\<close>

bnf "'a IF1"
  map: IF1map
  sets: IF1set
  bd: IFbd
  wits: IF1wit
  rel: IF1rel
           apply -
           apply (rule IF1map_id)
          apply (rule IF1map_comp)
         apply (erule IF1map_cong)
        apply (rule IF1set_natural)
       apply (rule IFbd_card_order)
      apply (rule IFbd_cinfinite)
     apply (rule IF1set_bd)
    apply (rule le_IF1rel_Comp)
   apply (rule IF1rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule IF1wit)
  done

bnf "'a IF2"
  map: IF2map
  sets: IF2set
  bd: IFbd
  wits: IF2wit
  rel: IF2rel
           apply -
           apply (rule IF2map_id)
          apply (rule IF2map_comp)
         apply (erule IF2map_cong)
        apply (rule IF2set_natural)
       apply (rule IFbd_card_order)
      apply (rule IFbd_cinfinite)
     apply (rule IF2set_bd)
    apply (rule le_IF2rel_Comp)
   apply (rule IF2rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule IF2wit)
  done

(*<*)
end
(*>*)
