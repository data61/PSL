(*  Title:       GFP
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Greatest Fixpoint (a.k.a. Codatatype)\<close>

(*<*)
theory GFP
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

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

ML \<open>open Ctr_Sugar_Util\<close>
declare [[bnf_internals]]
bnf_axiomatization (F1set1: 'a, F1set2: 'b1, F1set3: 'b2)  F1
  [wits: "'a \<Rightarrow> 'b1 \<Rightarrow> ('a, 'b1, 'b2) F1" "'a \<Rightarrow> 'b2 \<Rightarrow> ('a, 'b1, 'b2) F1"]
  for map: F1map rel: F1rel

bnf_axiomatization (F2set1: 'a, F2set2: 'b1, F2set3: 'b2)  F2
  [wits: "('a, 'b1, 'b2) F2"]
  for map: F2map rel: F2rel

lemma F1rel_cong: "\<lbrakk>R1 = S1; R2 = S2; R3 = S3\<rbrakk> \<Longrightarrow> F1rel R1 R2 R3 = F1rel S1 S2 S3"
  by hypsubst rule

lemma F2rel_cong: "\<lbrakk>R1 = S1; R2 = S2; R3 = S3\<rbrakk> \<Longrightarrow> F2rel R1 R2 R3 = F2rel S1 S2 S3"
  by hypsubst rule

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
lemmas F1in_mono23' = subsetD[OF F1in_mono23]

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
lemmas F2in_mono23' = subsetD[OF F2in_mono23]

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

subsection \<open>Coalgebra\<close>

definition coalg where
  "coalg B1 B2 s1 s2 =
     ((\<forall>a \<in> B1. s1 a \<in> F1in (UNIV :: 'a set) B1 B2) \<and> (\<forall>a \<in> B2. s2 a \<in> F2in (UNIV :: 'a set) B1 B2))"

lemmas coalg_F1in = bspec[OF conjunct1[OF iffD1[OF coalg_def]]]
lemmas coalg_F2in = bspec[OF conjunct2[OF iffD1[OF coalg_def]]]

lemma coalg_F1set2:
  "\<lbrakk>coalg B1 B2 s1 s2; a \<in> B1\<rbrakk> \<Longrightarrow> F1set2 (s1 a) \<subseteq> B1"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF coalg_def]} 1\<close>)
  apply (erule conjE)
  apply (drule bspec[rotated])
   apply assumption
  apply (erule CollectE conjE)+
  apply assumption
  done

lemma coalg_F1set3:
  "\<lbrakk>coalg B1 B2 s1 s2; a \<in> B1\<rbrakk> \<Longrightarrow> F1set3 (s1 a) \<subseteq> B2"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF coalg_def]} 1\<close>)
  apply (erule conjE)
  apply (drule bspec[rotated])
   apply assumption
  apply (erule CollectE conjE)+
  apply assumption
  done

lemma coalg_F2set2:
  "\<lbrakk>coalg B1 B2 s1 s2; a \<in> B2\<rbrakk> \<Longrightarrow> F2set2 (s2 a) \<subseteq> B1"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF coalg_def]} 1\<close>)
  apply (erule conjE)
  apply (drule bspec[rotated])
   apply assumption
  apply (erule CollectE conjE)+
  apply assumption
  done

lemma coalg_F2set3:
  "\<lbrakk>coalg B1 B2 s1 s2; a \<in> B2\<rbrakk> \<Longrightarrow> F2set3 (s2 a) \<subseteq> B2"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF coalg_def]} 1\<close>)
  apply (erule conjE)
  apply (drule bspec[rotated])
   apply assumption
  apply (erule CollectE conjE)+
  apply assumption
  done


subsection\<open>Type-coalgebra\<close>

abbreviation "tcoalg s1 s2 \<equiv> coalg UNIV UNIV s1 s2"

lemma tcoalg: "tcoalg s1 s2"
  apply (tactic \<open>rtac @{context} (@{thm coalg_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule subset_UNIV)
   apply (rule conjI)
    apply (rule subset_UNIV)
   apply (rule subset_UNIV)
  apply (rule ballI)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule subset_UNIV)
  done


subsection \<open>Morphism\<close>

definition mor where
  "mor B1 B2 s1 s2 B1' B2' s1' s2' f g =
   (((\<forall>a \<in> B1. f a \<in> B1') \<and> (\<forall>a \<in> B2. g a \<in> B2')) \<and>
   ((\<forall>z \<in> B1. F1map (id :: 'a \<Rightarrow> 'a) f g (s1 z) = s1' (f z)) \<and>
     (\<forall>z \<in> B2. F2map (id :: 'a \<Rightarrow> 'a) f g (s2 z) = s2' (g z))))"

lemma mor_image1: "mor B1 B2 s1 s2 B1' B2' s1' s2' f g \<Longrightarrow> f ` B1 \<subseteq> B1'"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (rule image_subsetI)
  apply (erule bspec)
  apply assumption
  done

lemma mor_image2: "mor B1 B2 s1 s2 B1' B2' s1' s2' f g \<Longrightarrow> g ` B2 \<subseteq> B2'"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (rule image_subsetI)
  apply (erule bspec)
  apply assumption
  done

lemmas mor_image1' = subsetD[OF mor_image1 imageI]
lemmas mor_image2' = subsetD[OF mor_image2 imageI]

lemma morE1: "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g; z \<in> B1\<rbrakk>
   \<Longrightarrow> F1map id f g (s1 z) = s1' (f z)"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply assumption
  done

lemma morE2: "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g; z \<in> B2\<rbrakk>
   \<Longrightarrow> F2map id f g (s2 z) = s2' (g z)"
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
    apply (rule ssubst_mem[OF id_apply])
    apply (erule subsetD)
    apply assumption

   apply (rule ballI)
   apply (rule ssubst_mem[OF id_apply])
   apply (erule subsetD)
   apply assumption

  apply (rule conjI)
   apply (rule ballI)
   apply (rule trans[OF F1.map_id])
   apply (rule sym)
   apply (rule arg_cong[OF id_apply])
  apply (rule ballI)
  apply (rule trans[OF F2.map_id])
  apply (rule sym)
  apply (rule arg_cong[OF id_apply])
  done

lemmas mor_id = mor_incl[OF subset_refl subset_refl]

lemma mor_comp:
  "\<lbrakk>mor B1 B2 s1 s2 B1' B2' s1' s2' f g;
    mor B1' B2' s1' s2' B1'' B2'' s1'' s2'' f' g'\<rbrakk> \<Longrightarrow>
   mor B1 B2 s1 s2 B1'' B2'' s1'' s2'' (f' o f) (g' o g)"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)

   apply (rule conjI)
    apply (rule ballI)
    apply (rule ssubst_mem[OF o_apply])
    apply (erule mor_image1')
    apply (erule mor_image1')
    apply assumption

   apply (rule ballI)
   apply (rule ssubst_mem[OF o_apply])
   apply (erule mor_image2')
   apply (erule mor_image2')
   apply assumption

  apply (rule conjI)
   apply (rule ballI)
   apply (tactic \<open>stac @{context} @{thm o_apply} 1\<close>)
   apply (rule trans)
    apply (rule sym[OF F1map_comp_id])
   apply (rule trans)
    apply (erule arg_cong[OF morE1])
    apply assumption
   apply (erule morE1)
   apply (erule mor_image1')
   apply assumption

  apply (rule ballI)
  apply (tactic \<open>stac @{context} @{thm o_apply} 1\<close>)
  apply (rule trans)
   apply (rule sym[OF F2map_comp_id])
  apply (rule trans)
   apply (erule arg_cong[OF morE2])
   apply assumption
  apply (erule morE2)
  apply (erule mor_image2')
  apply assumption
  done

lemma mor_cong: "\<lbrakk> f' = f; g' = g; mor B1 B2 s1 s2 B1' B2' s1' s2' f g\<rbrakk> \<Longrightarrow>
  mor B1 B2 s1 s2 B1' B2' s1' s2' f' g'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma mor_UNIV: "mor UNIV UNIV s1 s2 UNIV UNIV s1' s2' f1 f2 \<longleftrightarrow>
  F1map id f1 f2 o s1 = s1' o f1 \<and> F2map id f1 f2 o s2 = s2' o f2"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule ext)
    apply (rule trans)
     apply (rule trans)
      apply (rule o_apply)
     apply (erule morE1)
     apply (rule UNIV_I)
    apply (rule sym[OF o_apply])
   apply (rule ext)
   apply (rule trans)
    apply (rule trans)
     apply (rule o_apply)
    apply (erule morE2)
    apply (rule UNIV_I)
   apply (rule sym[OF o_apply])

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
   apply (rule UNIV_I)
  apply (rule conjI)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule ballI)
   apply (erule o_eq_dest)
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (rule ballI)
  apply (erule o_eq_dest)
  done

lemma mor_str:
  "mor UNIV UNIV s1 s2 UNIV UNIV (F1map id s1 s2) (F2map id s1 s2) s1 s2"
  apply (rule iffD2)
   apply (rule mor_UNIV)
  apply (rule conjI)
   apply (rule refl)
  apply (rule refl)
  done

lemma mor_case_sum:
  "mor UNIV UNIV s1 s2 UNIV UNIV (case_sum (F1map id Inl Inl o s1) s1') (case_sum (F2map id Inl Inl o s2) s2') Inl Inl"
  apply (tactic \<open>rtac @{context} (@{thm mor_UNIV} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule sym)
   apply (rule case_sum_o_inj(1))
  apply (rule sym)
  apply (rule case_sum_o_inj(1))
  done

subsection \<open>Bisimulations\<close>

definition bis where
  "bis B1 B2 s1 s2 B1' B2' s1' s2' R1 R2 =
   ((R1 \<subseteq> B1 \<times> B1' \<and> R2 \<subseteq> B2 \<times> B2') \<and>
   ((\<forall>b1 b1'. (b1, b1') \<in> R1 \<longrightarrow>
     (\<exists>z \<in> F1in UNIV R1 R2.
       F1map id fst fst z = s1 b1 \<and> F1map id snd snd z = s1' b1')) \<and>
    (\<forall>b2 b2'. (b2, b2') \<in> R2 \<longrightarrow>
     (\<exists>z \<in> F2in UNIV R1 R2.
       F2map id fst fst z = s2 b2 \<and> F2map id snd snd z = s2' b2'))))"

lemma bis_cong: "\<lbrakk>bis B1 B2 s1 s2 B1' B2' s1' s2' R1 R2; R1' = R1; R2' = R2\<rbrakk> \<Longrightarrow>
  bis B1 B2 s1 s2 B1' B2' s1' s2' R1' R2'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma bis_Frel:
  "bis B1 B2 s1 s2 B1' B2' s1' s2' R1 R2 \<longleftrightarrow>
  (R1 \<subseteq> B1 \<times> B1' \<and> R2 \<subseteq> B2 \<times> B2') \<and>
  ((\<forall> b1 b1'. (b1, b1') \<in> R1 \<longrightarrow> F1rel (=) (in_rel R1) (in_rel R2) (s1 b1) (s1' b1')) \<and>
   (\<forall> b2 b2'. (b2, b2') \<in> R2 \<longrightarrow> F2rel (=) (in_rel R1) (in_rel R2) (s2 b2) (s2' b2')))"
  apply (rule trans[OF bis_def])
  apply (rule iffI)
   apply (erule conjE)
   apply (erule conjI)

   apply (rule conjI)
    apply (rule allI)
    apply (rule allI)
    apply (rule impI)
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule allE)+
    apply (erule impE)
     apply assumption
    apply (erule bexE)
    apply (erule conjE CollectE)+
    apply (rule iffD2[OF F1.in_rel])
    apply (rule exI)
    apply (rule conjI[rotated])
     apply (rule conjI)
      apply (rule trans)
       apply (rule trans)
        apply (rule F1.map_comp)
       apply (rule F1.map_cong0)
         apply (rule fst_diag_id)
        apply (rule fun_cong[OF o_id])
       apply (rule fun_cong[OF o_id])
      apply assumption

     apply (rule trans)
      apply (rule trans)
       apply (rule F1.map_comp)
      apply (rule F1.map_cong0)
        apply (rule snd_diag_id)
       apply (rule fun_cong[OF o_id])
      apply (rule fun_cong[OF o_id])
     apply assumption

    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(1))
     apply (rule subset_trans)
      apply (erule image_mono)
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule refl)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule trans)
       apply (rule F1.set_map(2))
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (erule Collect_case_prod_in_rel_leI)
    apply (rule ord_eq_le_trans)
     apply (rule trans)
      apply (rule F1.set_map(3))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply (erule Collect_case_prod_in_rel_leI)

   apply (rule allI)
   apply (rule allI)
   apply (rule impI)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule allE)+
   apply (erule impE)
    apply assumption
   apply (erule bexE)
   apply (erule conjE CollectE)+
   apply (rule iffD2[OF F2.in_rel])
   apply (rule exI)
   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans)
      apply (rule trans)
       apply (rule F2.map_comp)
      apply (rule F2.map_cong0)
        apply (rule fst_diag_id)
       apply (rule fun_cong[OF o_id])
      apply (rule fun_cong[OF o_id])
     apply assumption

    apply (rule trans)
     apply (rule trans)
      apply (rule F2.map_comp)
     apply (rule F2.map_cong0)
       apply (rule snd_diag_id)
      apply (rule fun_cong[OF o_id])
     apply (rule fun_cong[OF o_id])
    apply assumption

   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(1))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule refl)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule trans)
      apply (rule F2.set_map(2))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply (erule Collect_case_prod_in_rel_leI)
   apply (rule ord_eq_le_trans)
    apply (rule trans)
     apply (rule F2.set_map(3))
    apply (rule trans[OF fun_cong[OF image_id] id_apply])
   apply (erule Collect_case_prod_in_rel_leI)

  apply (erule conjE)
  apply (erule conjI)

  apply (rule conjI)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule allI)
   apply (rule allI)
   apply (rule impI)
   apply (erule allE)
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (drule iffD1[OF F1.in_rel])
   apply (erule exE conjE CollectE Collect_case_prod_in_rel_leE)+

(*F1rel_bis_su*)
   apply (rule bexI)
    apply (rule conjI)
     apply (rule trans)
      apply (rule F1.map_comp)
     apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
     apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
     apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
     apply assumption

    apply (rule trans)
     apply (rule F1.map_comp)
    apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
    apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
    apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
    apply (rule trans)
     apply (rule F1.map_cong0)
       apply (rule Collect_case_prodD)
       apply (erule subsetD)
       apply assumption
      apply (rule refl)
     apply (rule refl)
    apply assumption

   apply (rule CollectI)
   apply (rule conjI)
    apply (rule subset_UNIV)

   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule trans)
      apply (rule F1.set_map(2))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption

   apply (rule ord_eq_le_trans)
    apply (rule trans)
     apply (rule F1.set_map(3))
    apply (rule trans[OF fun_cong[OF image_id] id_apply])
   apply assumption

  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply (drule iffD1[OF F2.in_rel])
  apply (erule exE conjE CollectE Collect_case_prod_in_rel_leE)+

(*F2rel_bis_su*)
  apply (rule bexI)
   apply (rule conjI)
    apply (rule trans)
     apply (rule F2.map_comp)
    apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
    apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
    apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
    apply assumption

   apply (rule trans)
    apply (rule F2.map_comp)
   apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
   apply (rule trans)
    apply (rule F2.map_cong0)
      apply (rule Collect_case_prodD)
      apply (erule subsetD)
      apply assumption
     apply (rule refl)
    apply (rule refl)
   apply assumption

  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)

  apply (rule conjI)
   apply (rule ord_eq_le_trans)
    apply (rule trans)
     apply (rule F2.set_map(2))
    apply (rule trans[OF fun_cong[OF image_id] id_apply])
   apply assumption

  apply (rule ord_eq_le_trans)
   apply (rule trans)
    apply (rule F2.set_map(3))
   apply (rule trans[OF fun_cong[OF image_id] id_apply])
  apply assumption
  done

lemma bis_converse:
  "bis B1 B2 s1 s2 B1' B2' s1' s2' R1 R2 \<Longrightarrow>
   bis B1' B2' s1' s2' B1 B2 s1 s2 (R1^-1) (R2^-1)"
  apply (tactic \<open>rtac @{context} (@{thm bis_Frel} RS iffD2) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm bis_Frel} RS iffD1) 1\<close>)
  apply (erule conjE)+
  apply (rule conjI)

   apply (rule conjI)
    apply (rule iffD1[OF converse_subset_swap])
    apply (erule subset_trans)
    apply (rule equalityD2)
    apply (rule converse_Times)

   apply (rule iffD1[OF converse_subset_swap])
   apply (erule subset_trans)
   apply (rule equalityD2)
   apply (rule converse_Times)

  apply (rule conjI)
   apply (rule allI)
   apply (rule allI)
   apply (rule impI)
   apply (rule predicate2D[OF eq_refl[OF F1rel_cong]])
      apply (rule conversep_eq)
     apply (rule conversep_in_rel)
    apply (rule conversep_in_rel)
   apply (rule predicate2D[OF eq_refl[OF sym[OF F1.rel_conversep]]])
   apply (erule allE)+
   apply (rule conversepI)
   apply (erule mp)
   apply (erule converseD)

  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule predicate2D[OF eq_refl[OF F2rel_cong]])
     apply (rule conversep_eq)
    apply (rule conversep_in_rel)
   apply (rule conversep_in_rel)
  apply (rule predicate2D[OF eq_refl[OF sym[OF F2.rel_conversep]]])
  apply (erule allE)+
  apply (rule conversepI)
  apply (erule mp)
  apply (erule converseD)
  done

lemma bis_Comp:
  "\<lbrakk>bis B1 B2 s1 s2 B1' B2' s1' s2' P1 P2;
    bis B1' B2' s1' s2' B1'' B2'' s1'' s2'' Q1 Q2\<rbrakk> \<Longrightarrow>
    bis B1 B2 s1 s2 B1'' B2'' s1'' s2'' (P1 O Q1) (P2 O Q2)"
  apply (tactic \<open>rtac @{context} (@{thm bis_Frel[THEN iffD2]}) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm bis_Frel[THEN iffD1]}) 1\<close>)+
  apply (erule conjE)+
  apply (rule conjI)
   apply (rule conjI)
    apply (erule relcomp_subset_Sigma)
    apply assumption
   apply (erule relcomp_subset_Sigma)
   apply assumption

  apply (rule conjI)
   apply (rule allI)+
   apply (rule impI)
   apply (rule predicate2D[OF eq_refl[OF F1rel_cong]])
      apply (rule eq_OO)
     apply (rule relcompp_in_rel)
    apply (rule relcompp_in_rel)
   apply (rule predicate2D[OF eq_refl[OF sym[OF F1.rel_compp]]])
   apply (erule relcompE)
   apply (tactic \<open>dtac @{context} (@{thm prod.inject[THEN iffD1]}) 1\<close>)
   apply (erule conjE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule allE)+
   apply (rule relcomppI)
    apply (erule mp)
    apply assumption
   apply (erule mp)
   apply assumption

  apply (rule allI)+
  apply (rule impI)
  apply (rule predicate2D[OF eq_refl[OF F2rel_cong]])
     apply (rule eq_OO)
    apply (rule relcompp_in_rel)
   apply (rule relcompp_in_rel)
  apply (rule predicate2D[OF eq_refl[OF sym[OF F2.rel_compp]]])
  apply (erule relcompE)
  apply (tactic \<open>dtac @{context} (@{thm prod.inject[THEN iffD1]}) 1\<close>)
  apply (erule conjE)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule allE)+
  apply (rule relcomppI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

lemma bis_Gr: "\<lbrakk>coalg B1 B2 s1 s2; mor B1 B2 s1 s2 B1' B2' s1' s2' f1 f2\<rbrakk> \<Longrightarrow>
   bis B1 B2 s1 s2 B1' B2' s1' s2' (BNF_Def.Gr B1 f1) (BNF_Def.Gr B2 f2)"
  unfolding bis_Frel eq_alt in_rel_Gr F1.rel_Grp F2.rel_Grp
  apply (rule conjI)
   apply (rule conjI)
    apply (rule iffD2[OF Gr_incl])
    apply (erule mor_image1)
   apply (rule iffD2[OF Gr_incl])
   apply (erule mor_image2)

  apply (rule conjI)
   apply (rule allI)
   apply (rule allI)
   apply (rule impI)
   apply (rule GrpI)
    apply (erule trans[OF morE1])
     apply (erule GrD1)
    apply (erule arg_cong[OF GrD2])
   apply (erule coalg_F1in)
   apply (erule GrD1)

  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule GrpI)
   apply (erule trans[OF morE2])
    apply (erule GrD1)
   apply (erule arg_cong[OF GrD2])
  apply (erule coalg_F2in)
  apply (erule GrD1)
  done

lemmas bis_image2 = bis_cong[OF bis_Comp[OF bis_converse[OF bis_Gr] bis_Gr] image2_Gr image2_Gr]
lemmas bis_diag = bis_cong[OF bis_Gr[OF _ mor_id] Id_on_Gr Id_on_Gr]

lemma bis_Union: "\<forall>i \<in> I. bis B1 B2 s1 s2 B1 B2 s1 s2 (R1i i) (R2i i) \<Longrightarrow>
  bis B1 B2 s1 s2 B1 B2 s1 s2 (\<Union>i\<in> I. R1i i) (\<Union>i\<in> I. R2i i)"
  unfolding bis_def
  apply (rule conjI)
   apply (rule conjI)
    apply (rule UN_least)
    apply (drule bspec)
     apply assumption
    apply (drule conjunct1)
    apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule UN_least)
   apply (drule bspec)
    apply assumption
   apply (drule conjunct1)
   apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)

  apply (rule conjI)
   apply (rule allI)+
   apply (rule impI)
   apply (erule UN_E)
   apply (drule bspec)
    apply assumption
   apply (drule conjunct2)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule allE)+
   apply (drule mp)
    apply assumption
   apply (erule bexE)
   apply (rule bexI)
    apply assumption
   apply (rule F1in_mono23')
     apply (erule SUP_upper2[OF _ subset_refl])
    apply (erule SUP_upper2[OF _ subset_refl])
   apply assumption

  apply (rule allI)+
  apply (rule impI)
  apply (erule UN_E)
  apply (drule bspec)
   apply assumption
  apply (drule conjunct2)
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule allE)+
  apply (drule mp)
   apply assumption
  apply (erule bexE)
  apply (rule bexI)
   apply assumption
  apply (rule F2in_mono23')
    apply (erule SUP_upper2[OF _ subset_refl])
   apply (erule SUP_upper2[OF _ subset_refl])
  apply assumption
  done

(* self-bisimulation: *)
abbreviation "sbis B1 B2 s1 s2 R1 R2 \<equiv> bis B1 B2 s1 s2 B1 B2 s1 s2 R1 R2"

(* The greatest self-bisimulation *)
definition lsbis1 where "lsbis1 B1 B2 s1 s2 =
  (\<Union>R \<in> {(R1, R2) | R1 R2 . sbis B1 B2 s1 s2 R1 R2}. fst R)"

definition lsbis2 where "lsbis2 B1 B2 s1 s2 =
  (\<Union>R \<in> {(R1, R2) | R1 R2 . sbis B1 B2 s1 s2 R1 R2}. snd R)"

lemma sbis_lsbis:
  "sbis B1 B2 s1 s2 (lsbis1 B1 B2 s1 s2) (lsbis2 B1 B2 s1 s2)"
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm bis_cong}) 1\<close>)
    apply (rule lsbis1_def)
   apply (rule lsbis2_def)
  apply (rule bis_Union)
  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule bis_cong)
   apply (rule fst_conv)
  apply (rule snd_conv)
  done

lemmas lsbis1_incl = conjunct1[OF conjunct1[OF iffD1[OF bis_def]], OF sbis_lsbis]
lemmas lsbis2_incl = conjunct2[OF conjunct1[OF iffD1[OF bis_def]], OF sbis_lsbis]
lemmas lsbisE1 =
  mp[OF spec[OF spec[OF conjunct1[OF conjunct2[OF iffD1[OF bis_def]], OF sbis_lsbis]]]]
lemmas lsbisE2 =
  mp[OF spec[OF spec[OF conjunct2[OF conjunct2[OF iffD1[OF bis_def]], OF sbis_lsbis]]]]

lemma incl_lsbis1: "sbis B1 B2 s1 s2 R1 R2 \<Longrightarrow> R1 \<subseteq> lsbis1 B1 B2 s1 s2"
  apply (rule xt1(3))
   apply (rule lsbis1_def)
  apply (rule SUP_upper2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
  apply (rule equalityD2)
  apply (rule fst_conv)
  done

lemma incl_lsbis2: "sbis B1 B2 s1 s2 R1 R2 \<Longrightarrow> R2 \<subseteq> lsbis2 B1 B2 s1 s2"
  apply (rule xt1(3))
   apply (rule lsbis2_def)
  apply (rule SUP_upper2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
  apply (rule equalityD2)
  apply (rule snd_conv)
  done

lemma equiv_lsbis1: "coalg B1 B2 s1 s2 \<Longrightarrow> equiv B1 (lsbis1 B1 B2 s1 s2)"
  apply (rule iffD2[OF equiv_def])

  apply (rule conjI)
   apply (rule iffD2[OF refl_on_def])
   apply (rule conjI)
    apply (rule lsbis1_incl)
   apply (rule ballI)
   apply (rule subsetD)
    apply (rule incl_lsbis1)
    apply (rule bis_diag)
    apply assumption
   apply (erule Id_onI)

  apply (rule conjI)
   apply (rule iffD2[OF sym_def])
   apply (rule allI)+
   apply (rule impI)
   apply (rule subsetD)
    apply (rule incl_lsbis1)
    apply (rule bis_converse)
    apply (rule sbis_lsbis)
   apply (erule converseI)

  apply (rule iffD2[OF trans_def])
  apply (rule allI)+
  apply (rule impI)+
  apply (rule subsetD)
   apply (rule incl_lsbis1)
   apply (rule bis_Comp)
    apply (rule sbis_lsbis)
   apply (rule sbis_lsbis)
  apply (erule relcompI)
  apply assumption
  done

lemma equiv_lsbis2: "coalg B1 B2 s1 s2 \<Longrightarrow> equiv B2 (lsbis2 B1 B2 s1 s2)"
  unfolding equiv_def refl_on_def sym_def trans_def
  apply (rule conjI)

   apply (rule conjI)
    apply (rule lsbis2_incl)
   apply (rule ballI)
   apply (rule subsetD)
    apply (rule incl_lsbis2)
    apply (rule bis_diag)
    apply assumption
   apply (erule Id_onI)

  apply (rule conjI)

   apply (rule allI)+
   apply (rule impI)
   apply (rule subsetD)
    apply (rule incl_lsbis2)
    apply (rule bis_converse)
    apply (rule sbis_lsbis)
   apply (erule converseI)

  apply (rule allI)+
  apply (rule impI)+
  apply (rule subsetD)
   apply (rule incl_lsbis2)
   apply (rule bis_Comp)
    apply (rule sbis_lsbis)
   apply (rule sbis_lsbis)
  apply (erule relcompI)
  apply assumption
  done


subsection \<open>The Tree Coalgebra\<close>

typedef bd_type_F = "UNIV :: (bd_type_F1 + bd_type_F2) set"
  apply (rule exI) apply (rule UNIV_I)
  done

type_synonym 'a carrier = "((bd_type_F + bd_type_F) list set \<times>
  ((bd_type_F + bd_type_F) list \<Rightarrow> ('a, bd_type_F, bd_type_F) F1 + ('a, bd_type_F, bd_type_F) F2))"

abbreviation "bd_F \<equiv> dir_image (bd_F1 +c bd_F2) Abs_bd_type_F"
lemmas bd_F = dir_image[OF Abs_bd_type_F_inject[OF UNIV_I UNIV_I] Card_order_csum]
lemmas bd_F_Cinfinite = Cinfinite_cong[OF bd_F Cinfinite_csum1[OF F1.bd_Cinfinite]]
lemmas bd_F_Card_order = Card_order_ordIso[OF Card_order_csum ordIso_symmetric[OF bd_F]]
lemma bd_F_card_order: "card_order bd_F"
  apply (rule card_order_dir_image)
   apply (rule bijI')
    apply (rule Abs_bd_type_F_inject[OF UNIV_I UNIV_I])
   apply (rule Abs_bd_type_F_cases)
   apply (erule exI)
  apply (rule card_order_csum)
   apply (rule F1.bd_card_order)
  apply (rule F2.bd_card_order)
  done

lemmas F1set1_bd' = ordLeq_transitive[OF F1.set_bd(1) ordLeq_ordIso_trans[OF ordLeq_csum1[OF F1.bd_Card_order] bd_F]]
lemmas F1set2_bd' = ordLeq_transitive[OF F1.set_bd(2) ordLeq_ordIso_trans[OF ordLeq_csum1[OF F1.bd_Card_order] bd_F]]
lemmas F1set3_bd' = ordLeq_transitive[OF F1.set_bd(3) ordLeq_ordIso_trans[OF ordLeq_csum1[OF F1.bd_Card_order] bd_F]]

lemmas F2set1_bd' = ordLeq_transitive[OF F2.set_bd(1) ordLeq_ordIso_trans[OF ordLeq_csum2[OF F2.bd_Card_order] bd_F]]
lemmas F2set2_bd' = ordLeq_transitive[OF F2.set_bd(2) ordLeq_ordIso_trans[OF ordLeq_csum2[OF F2.bd_Card_order] bd_F]]
lemmas F2set3_bd' = ordLeq_transitive[OF F2.set_bd(3) ordLeq_ordIso_trans[OF ordLeq_csum2[OF F2.bd_Card_order] bd_F]]

abbreviation "Succ1 Kl kl \<equiv> {k1. Inl k1 \<in> BNF_Greatest_Fixpoint.Succ Kl kl}"
abbreviation "Succ2 Kl kl \<equiv> {k2. Inr k2 \<in> BNF_Greatest_Fixpoint.Succ Kl kl}"

definition isNode1 where
  "isNode1 Kl lab kl = (\<exists>x1. lab kl = Inl x1 \<and> F1set2 x1 = Succ1 Kl kl \<and> F1set3 x1 = Succ2 Kl kl)"

definition isNode2 where
  "isNode2 Kl lab kl = (\<exists>x2. lab kl = Inr x2 \<and> F2set2 x2 = Succ1 Kl kl \<and> F2set3 x2 = Succ2 Kl kl)"

abbreviation isTree where
  "isTree Kl lab \<equiv> ([] \<in> Kl \<and>
 (\<forall>kl \<in> Kl. (\<forall>k1 \<in> Succ1 Kl kl. isNode1 Kl lab (kl @ [Inl k1])) \<and>
            (\<forall>k2 \<in> Succ2 Kl kl. isNode2 Kl lab (kl @ [Inr k2]))))"

definition carT1 where
  "carT1 = {(Kl :: (bd_type_F + bd_type_F) list set, lab) | Kl lab. isTree Kl lab \<and> isNode1 Kl lab []}"

definition carT2 where
  "carT2 = {(Kl :: (bd_type_F + bd_type_F) list set, lab) | Kl lab. isTree Kl lab \<and> isNode2 Kl lab []}"

definition strT1 where
  "strT1 = (case_prod (%Kl lab. case_sum (F1map id
       (\<lambda>k1. (BNF_Greatest_Fixpoint.Shift Kl (Inl k1), BNF_Greatest_Fixpoint.shift lab (Inl k1)))
       (\<lambda>k2. (BNF_Greatest_Fixpoint.Shift Kl (Inr k2), BNF_Greatest_Fixpoint.shift lab (Inr k2)))) undefined (lab [])))"

definition strT2 where
  "strT2 = (case_prod (%Kl lab. case_sum undefined (F2map id
       (\<lambda>k1. (BNF_Greatest_Fixpoint.Shift Kl (Inl k1), BNF_Greatest_Fixpoint.shift lab (Inl k1)))
       (\<lambda>k2. (BNF_Greatest_Fixpoint.Shift Kl (Inr k2), BNF_Greatest_Fixpoint.shift lab (Inr k2)))) (lab [])))"

lemma coalg_T: "coalg carT1 carT2 strT1 strT2"
  unfolding coalg_def carT1_def carT2_def isNode1_def isNode2_def
  apply (rule conjI)
   apply (rule ballI)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule ssubst_mem[OF trans[OF trans[OF fun_cong[OF strT1_def] prod.case]]])
    apply (erule trans[OF arg_cong])
    apply (rule sum.case(1))
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule subset_UNIV)
   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(2)])
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (rule conjI)
     apply (rule conjI)
      apply (erule empty_Shift)
      apply (drule rev_subsetD)
       apply (erule equalityD1)
      apply (erule CollectD)
     apply (rule ballI)
     apply (rule conjI)
      apply (rule ballI)
      apply (erule CollectE)
      apply (drule ShiftD)
      apply (drule bspec)
       apply (erule thin_rl)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule bspec)
       apply (rule CollectI)
       apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
      apply (erule exE conjE)+
      apply (rule exI)
      apply (rule conjI)
       apply (rule trans[OF fun_cong[OF shift_def]])
       apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
       apply assumption
      apply (rule conjI)
       apply (erule trans)
       apply (rule Collect_cong)
       apply (rule eqset_imp_iff)
       apply (rule sym)
       apply (rule trans)
        apply (rule Succ_Shift)
       apply (rule arg_cong[OF sym[OF append_Cons]])
      apply (erule trans)
      apply (rule Collect_cong)
      apply (rule eqset_imp_iff)
      apply (rule sym)
      apply (rule trans)
       apply (rule Succ_Shift)
      apply (rule arg_cong[OF sym[OF append_Cons]])


     apply (rule ballI)
     apply (erule CollectE)
     apply (drule ShiftD)
     apply (drule bspec)
      apply (erule thin_rl)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule bspec)
      apply (rule CollectI)
      apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
     apply (erule exE conjE)+
     apply (rule exI)
     apply (rule conjI)
      apply (rule trans[OF fun_cong[OF shift_def]])
      apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
      apply assumption
     apply (rule conjI)
      apply (erule trans)
      apply (rule Collect_cong)
      apply (rule eqset_imp_iff)
      apply (rule sym)
      apply (rule trans)
       apply (rule Succ_Shift)
      apply (rule arg_cong[OF sym[OF append_Cons]])
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])

    apply (drule bspec)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule bspec)
     apply (erule subsetD[OF equalityD1])
     apply assumption
    apply (erule exE conjE)+
    apply (rule exI)
    apply (rule conjI)
     apply (rule trans[OF fun_cong[OF shift_def]])
     apply (erule trans[OF arg_cong[OF sym[OF append_Nil]]])
    apply (rule conjI)
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Nil]])
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Nil]])

   apply (rule ord_eq_le_trans[OF F1.set_map(3)])
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule conjI)
    apply (rule conjI)
     apply (erule empty_Shift)
     apply (drule rev_subsetD)
      apply (erule equalityD1)
     apply (erule CollectD)
    apply (rule ballI)
    apply (rule conjI)
     apply (rule ballI)
     apply (erule CollectE)
     apply (drule ShiftD)
     apply (drule bspec)
      apply (erule thin_rl)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule bspec)
      apply (rule CollectI)
      apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
     apply (erule exE conjE)+
     apply (rule exI)
     apply (rule conjI)
      apply (rule trans[OF fun_cong[OF shift_def]])
      apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
      apply assumption
     apply (rule conjI)
      apply (erule trans)
      apply (rule Collect_cong)
      apply (rule eqset_imp_iff)
      apply (rule sym)
      apply (rule trans)
       apply (rule Succ_Shift)
      apply (rule arg_cong[OF sym[OF append_Cons]])
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])


    apply (rule ballI)
    apply (erule CollectE)
    apply (drule ShiftD)
    apply (drule bspec)
     apply (erule thin_rl)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule bspec)
     apply (rule CollectI)
     apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
    apply (erule exE conjE)+
    apply (rule exI)
    apply (rule conjI)
     apply (rule trans[OF fun_cong[OF shift_def]])
     apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
     apply assumption
    apply (rule conjI)
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Cons]])

   apply (drule bspec)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule bspec)
    apply (erule subsetD[OF equalityD1])
    apply assumption
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI)
    apply (rule trans[OF fun_cong[OF shift_def]])
    apply (erule trans[OF arg_cong[OF sym[OF append_Nil]]])
   apply (rule conjI)
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Nil]])
   apply (erule trans)
   apply (rule Collect_cong)
   apply (rule eqset_imp_iff)
   apply (rule sym)
   apply (rule trans)
    apply (rule Succ_Shift)
   apply (rule arg_cong[OF sym[OF append_Nil]])

(**)

  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule ssubst_mem[OF trans[OF fun_cong[OF strT2_def] prod.case]])
  apply (rule ssubst_mem)
   apply (rule trans)
    apply (erule arg_cong)
   apply (rule sum.case(2))
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(2)])
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule conjI)
    apply (rule conjI)
     apply (erule empty_Shift)
     apply (drule rev_subsetD)
      apply (erule equalityD1)
     apply (erule CollectD)
    apply (rule ballI)
    apply (rule conjI)
     apply (rule ballI)
     apply (erule CollectE)
     apply (drule ShiftD)
     apply (drule bspec)
      apply (erule thin_rl)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule bspec)
      apply (rule CollectI)
      apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
     apply (erule exE conjE)+
     apply (rule exI)
     apply (rule conjI)
      apply (rule trans[OF fun_cong[OF shift_def]])
      apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
      apply assumption
     apply (rule conjI)
      apply (erule trans)
      apply (rule Collect_cong)
      apply (rule eqset_imp_iff)
      apply (rule sym)
      apply (rule trans)
       apply (rule Succ_Shift)
      apply (rule arg_cong[OF sym[OF append_Cons]])
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])


    apply (rule ballI)
    apply (erule CollectE)
    apply (drule ShiftD)
    apply (drule bspec)
     apply (erule thin_rl)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule bspec)
     apply (rule CollectI)
     apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
    apply (erule exE conjE)+
    apply (rule exI)
    apply (rule conjI)
     apply (rule trans[OF fun_cong[OF shift_def]])
     apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
     apply assumption
    apply (rule conjI)
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Cons]])

   apply (drule bspec)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (drule bspec)
    apply (erule subsetD[OF equalityD1])
    apply assumption
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI)
    apply (rule trans[OF fun_cong[OF shift_def]])
    apply (erule trans[OF arg_cong[OF sym[OF append_Nil]]])
   apply (rule conjI)
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Nil]])
   apply (erule trans)
   apply (rule Collect_cong)
   apply (rule eqset_imp_iff)
   apply (rule sym)
   apply (rule trans)
    apply (rule Succ_Shift)
   apply (rule arg_cong[OF sym[OF append_Nil]])

  apply (rule ord_eq_le_trans[OF F2.set_map(3)])
  apply (rule image_subsetI)
  apply (rule CollectI)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule refl)
  apply (rule conjI)
   apply (rule conjI)
    apply (erule empty_Shift)
    apply (drule rev_subsetD)
     apply (erule equalityD1)
    apply (erule CollectD)
   apply (rule ballI)
   apply (rule conjI)
    apply (rule ballI)
    apply (erule CollectE)
    apply (drule ShiftD)
    apply (drule bspec)
     apply (erule thin_rl)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule bspec)
     apply (rule CollectI)
     apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
    apply (erule exE conjE)+
    apply (rule exI)
    apply (rule conjI)
     apply (rule trans[OF fun_cong[OF shift_def]])
     apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
     apply assumption
    apply (rule conjI)
     apply (erule trans)
     apply (rule Collect_cong)
     apply (rule eqset_imp_iff)
     apply (rule sym)
     apply (rule trans)
      apply (rule Succ_Shift)
     apply (rule arg_cong[OF sym[OF append_Cons]])
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Cons]])


   apply (rule ballI)
   apply (erule CollectE)
   apply (drule ShiftD)
   apply (drule bspec)
    apply (erule thin_rl)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule bspec)
    apply (rule CollectI)
    apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI)
    apply (rule trans[OF fun_cong[OF shift_def]])
    apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
    apply assumption
   apply (rule conjI)
    apply (erule trans)
    apply (rule Collect_cong)
    apply (rule eqset_imp_iff)
    apply (rule sym)
    apply (rule trans)
     apply (rule Succ_Shift)
    apply (rule arg_cong[OF sym[OF append_Cons]])
   apply (erule trans)
   apply (rule Collect_cong)
   apply (rule eqset_imp_iff)
   apply (rule sym)
   apply (rule trans)
    apply (rule Succ_Shift)
   apply (rule arg_cong[OF sym[OF append_Cons]])

  apply (drule bspec)
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (drule bspec)
   apply (erule subsetD[OF equalityD1])
   apply assumption
  apply (erule exE conjE)+
  apply (rule exI)
  apply (rule conjI)
   apply (rule trans[OF fun_cong[OF shift_def]])
   apply (erule trans[OF arg_cong[OF sym[OF append_Nil]]])
  apply (rule conjI)
   apply (erule trans)
   apply (rule Collect_cong)
   apply (rule eqset_imp_iff)
   apply (rule sym)
   apply (rule trans)
    apply (rule Succ_Shift)
   apply (rule arg_cong[OF sym[OF append_Nil]])
  apply (erule trans)
  apply (rule Collect_cong)
  apply (rule eqset_imp_iff)
  apply (rule sym)
  apply (rule trans)
   apply (rule Succ_Shift)
  apply (rule arg_cong[OF sym[OF append_Nil]])
  done

abbreviation tobd_F12 where "tobd_F12 s1 x \<equiv> toCard (F1set2 (s1 x)) bd_F"
abbreviation tobd_F13 where "tobd_F13 s1 x \<equiv> toCard (F1set3 (s1 x)) bd_F"
abbreviation tobd_F22 where "tobd_F22 s2 x \<equiv> toCard (F2set2 (s2 x)) bd_F"
abbreviation tobd_F23 where "tobd_F23 s2 x \<equiv> toCard (F2set3 (s2 x)) bd_F"
abbreviation frombd_F12 where "frombd_F12 s1 x \<equiv> fromCard (F1set2 (s1 x)) bd_F"
abbreviation frombd_F13 where "frombd_F13 s1 x \<equiv> fromCard (F1set3 (s1 x)) bd_F"
abbreviation frombd_F22 where "frombd_F22 s2 x \<equiv> fromCard (F2set2 (s2 x)) bd_F"
abbreviation frombd_F23 where "frombd_F23 s2 x \<equiv> fromCard (F2set3 (s2 x)) bd_F"

lemmas tobd_F12_inj = toCard_inj[OF F1set2_bd' bd_F_Card_order]
lemmas tobd_F13_inj = toCard_inj[OF F1set3_bd' bd_F_Card_order]
lemmas tobd_F22_inj = toCard_inj[OF F2set2_bd' bd_F_Card_order]
lemmas tobd_F23_inj = toCard_inj[OF F2set3_bd' bd_F_Card_order]
lemmas frombd_F12_tobd_F12 = fromCard_toCard[OF F1set2_bd' bd_F_Card_order]
lemmas frombd_F13_tobd_F13 = fromCard_toCard[OF F1set3_bd' bd_F_Card_order]
lemmas frombd_F22_tobd_F22 = fromCard_toCard[OF F2set2_bd' bd_F_Card_order]
lemmas frombd_F23_tobd_F23 = fromCard_toCard[OF F2set3_bd' bd_F_Card_order]

(* the levels of the behavior of a via s, through the embedding in Field bd_F *)
definition Lev where
  "Lev s1 s2 = rec_nat (%a. {[]}, %b. {[]})
    (%n rec.
      (%a1.
        {Inl (tobd_F12 s1 a1 b1) # kl | b1 kl. b1 \<in> F1set2 (s1 a1) \<and> kl \<in> fst rec b1} \<union>
        {Inr (tobd_F13 s1 a1 b2) # kl | b2 kl. b2 \<in> F1set3 (s1 a1) \<and> kl \<in> snd rec b2},
       %a2.
        {Inl (tobd_F22 s2 a2 b1) # kl | b1 kl. b1 \<in> F2set2 (s2 a2) \<and> kl \<in> fst rec b1} \<union>
        {Inr (tobd_F23 s2 a2 b2) # kl | b2 kl. b2 \<in> F2set3 (s2 a2) \<and> kl \<in> snd rec b2}))"

abbreviation Lev1 where "Lev1 s1 s2 n \<equiv> fst (Lev s1 s2 n)"
abbreviation Lev2 where "Lev2 s1 s2 n \<equiv> snd (Lev s1 s2 n)"

lemmas Lev1_0 = fun_cong[OF fstI[OF rec_nat_0_imp[OF Lev_def]]]
lemmas Lev2_0 = fun_cong[OF sndI[OF rec_nat_0_imp[OF Lev_def]]]
lemmas Lev1_Suc = fun_cong[OF fstI[OF rec_nat_Suc_imp[OF Lev_def]]]
lemmas Lev2_Suc = fun_cong[OF sndI[OF rec_nat_Suc_imp[OF Lev_def]]]

(* recovery of the element corresponding to a path: *)
definition rv where
  "rv s1 s2 = rec_list (%b1. Inl b1, %b2. Inr b2)
    (%k kl rec.
      (%b1. case_sum (%k1. fst rec (frombd_F12 s1 b1 k1)) (%k2. snd rec (frombd_F13 s1 b1 k2)) k,
       %b2. case_sum (%k1. fst rec (frombd_F22 s2 b2 k1)) (%k2. snd rec (frombd_F23 s2 b2 k2)) k))"

abbreviation rv1 where "rv1 s1 s2 kl \<equiv> fst (rv s1 s2 kl)"
abbreviation rv2 where "rv2 s1 s2 kl \<equiv> snd (rv s1 s2 kl)"

lemmas rv1_Nil = fun_cong[OF fstI[OF rec_list_Nil_imp[OF rv_def]]]
lemmas rv2_Nil = fun_cong[OF sndI[OF rec_list_Nil_imp[OF rv_def]]]
lemmas rv1_Cons = fun_cong[OF fstI[OF rec_list_Cons_imp[OF rv_def]]]
lemmas rv2_Cons = fun_cong[OF sndI[OF rec_list_Cons_imp[OF rv_def]]]

(* the labels: *)
abbreviation "Lab1 s1 s2 b1 kl \<equiv>
  (case_sum (%k. Inl (F1map id (tobd_F12 s1 k) (tobd_F13 s1 k) (s1 k)))
                (%k. Inr (F2map id (tobd_F22 s2 k) (tobd_F23 s2 k) (s2 k))) (rv1 s1 s2 kl b1))"

abbreviation "Lab2 s1 s2 b2 kl \<equiv>
  (case_sum (%k. Inl (F1map id (tobd_F12 s1 k) (tobd_F13 s1 k) (s1 k)))
                (%k. Inr (F2map id (tobd_F22 s2 k) (tobd_F23 s2 k) (s2 k))) (rv2 s1 s2 kl b2))"

(* the behavior of a under s: *)
definition "beh1 s1 s2 a = (\<Union>n. Lev1 s1 s2 n a, Lab1 s1 s2 a)"
definition "beh2 s1 s2 a = (\<Union>n. Lev2 s1 s2 n a, Lab2 s1 s2 a)"

lemma length_Lev:
  "\<forall>kl b1 b2. (kl \<in> Lev1 s1 s2 n b1 \<longrightarrow> length kl = n) \<and>
              (kl \<in> Lev2 s1 s2 n b2 \<longrightarrow> length kl = n)"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule conjI)
    apply (rule impI)
    apply (drule subsetD[OF equalityD1[OF Lev1_0]])
    apply (erule singletonE)
    apply (erule ssubst)
    apply (rule list.size(3))

   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev2_0]])
   apply (erule singletonE)
   apply (erule ssubst)
   apply (rule list.size(3))

  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule trans)
     apply (rule length_Cons)
    apply (rule arg_cong[of _ _ Suc])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule trans)
    apply (rule length_Cons)
   apply (rule arg_cong[of _ _ Suc])
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply assumption


  apply (rule impI)
  apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
  apply (erule UnE)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule trans)
    apply (rule length_Cons)
   apply (rule arg_cong[of _ _ Suc])
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule mp)
   apply assumption

  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule trans)
   apply (rule length_Cons)
  apply (rule arg_cong[of _ _ Suc])
  apply (erule allE)+
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule mp)
  apply assumption
  done

lemmas length_Lev1 = mp[OF conjunct1[OF spec[OF spec [OF spec[OF length_Lev]]]]]
lemmas length_Lev2 = mp[OF conjunct2[OF spec[OF spec [OF spec[OF length_Lev]]]]]

lemma length_Lev1': "kl \<in> Lev1 s1 s2 n a \<Longrightarrow> kl \<in> Lev1 s1 s2 (length kl) a"
  apply (frule length_Lev1)
  apply (erule ssubst)
  apply assumption
  done

lemma length_Lev2': "kl \<in> Lev2 s1 s2 n a \<Longrightarrow> kl \<in> Lev2 s1 s2 (length kl) a"
  apply (frule length_Lev2)
  apply (erule ssubst)
  apply assumption
  done

lemma rv_last:
  "\<forall>k b1 b2.
   ((\<exists>b1'. rv1 s1 s2 (kl @ [Inl k]) b1 = Inl b1') \<and>
    (\<exists>b1'. rv1 s1 s2 (kl @ [Inr k]) b1 = Inr b1')) \<and>
   ((\<exists>b2'. rv2 s1 s2 (kl @ [Inl k]) b2 = Inl b2') \<and>
    (\<exists>b2'. rv2 s1 s2 (kl @ [Inr k]) b2 = Inr b2'))"
  apply (rule list.induct[of _ kl])
   apply (rule allI)+
   apply (rule conjI)
    apply (rule conjI)
     apply (rule exI)
     apply (rule trans[OF arg_cong[OF append_Nil]])
     apply (rule trans[OF rv1_Cons])
     apply (rule trans[OF arg_cong[OF sum.case(1)]])
     apply (rule rv1_Nil)
    apply (rule exI)
    apply (rule trans[OF arg_cong[OF append_Nil]])
    apply (rule trans[OF rv1_Cons])
    apply (rule trans[OF arg_cong[OF sum.case(2)]])
    apply (rule rv2_Nil)
   apply (rule conjI)
    apply (rule exI)
    apply (rule trans[OF arg_cong[OF append_Nil]])
    apply (rule trans[OF rv2_Cons])
    apply (rule trans[OF arg_cong[OF sum.case(1)]])
    apply (rule rv1_Nil)
   apply (rule exI)
   apply (rule trans[OF arg_cong[OF append_Nil]])
   apply (rule trans[OF rv2_Cons])
   apply (rule trans[OF arg_cong[OF sum.case(2)]])
   apply (rule rv2_Nil)

  apply (rule allI)+
  apply (rule sum.exhaust)
   apply (rule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (rule conjI)
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule exE)
     apply (rule exI)
     apply (rule trans[OF arg_cong[OF append_Cons]])
     apply (rule trans[OF rv1_Cons])
     apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
     apply (rule trans[OF arg_cong[OF sum.case(1)]])
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule exE)
    apply (rule exI)
    apply (rule trans[OF arg_cong[OF append_Cons]])
    apply (rule trans[OF rv1_Cons])
    apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
    apply (rule trans[OF arg_cong[OF sum.case(1)]])
    apply assumption

   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule conjI)
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule exE)
    apply (rule exI)
    apply (rule trans[OF arg_cong[OF append_Cons]])
    apply (rule trans[OF rv2_Cons])
    apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
    apply (rule trans[OF arg_cong[OF sum.case(1)]])
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule exE)
   apply (rule exI)
   apply (rule trans[OF arg_cong[OF append_Cons]])
   apply (rule trans[OF rv2_Cons])
   apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
   apply (rule trans[OF arg_cong[OF sum.case(1)]])
   apply assumption

  apply (rule conjI)
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (rule conjI)
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule exE)
    apply (rule exI)
    apply (rule trans[OF arg_cong[OF append_Cons]])
    apply (rule trans[OF rv1_Cons])
    apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
    apply (rule trans[OF arg_cong[OF sum.case(2)]])
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule exE)
   apply (rule exI)
   apply (rule trans[OF arg_cong[OF append_Cons]])
   apply (rule trans[OF rv1_Cons])
   apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
   apply (rule trans[OF arg_cong[OF sum.case(2)]])
   apply assumption

  apply (erule allE)+
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (rule conjI)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule exE)
   apply (rule exI)
   apply (rule trans[OF arg_cong[OF append_Cons]])
   apply (rule trans[OF rv2_Cons])
   apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
   apply (rule trans[OF arg_cong[OF sum.case(2)]])
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule exE)
  apply (rule exI)
  apply (rule trans[OF arg_cong[OF append_Cons]])
  apply (rule trans[OF rv2_Cons])
  apply (erule trans[OF arg_cong[OF sum.case_cong_weak]])
  apply (rule trans[OF arg_cong[OF sum.case(2)]])
  apply assumption
  done

lemmas rv_last' = spec[OF spec[OF spec[OF rv_last]]]
lemmas rv1_Inl_last = conjunct1[OF conjunct1[OF rv_last']]
lemmas rv1_Inr_last = conjunct2[OF conjunct1[OF rv_last']]
lemmas rv2_Inl_last = conjunct1[OF conjunct2[OF rv_last']]
lemmas rv2_Inr_last = conjunct2[OF conjunct2[OF rv_last']]

lemma Fset_Lev:
  "\<forall>kl b1 b2 b1' b2' b1'' b2''.
   (kl \<in> Lev1 s1 s2 n b1 \<longrightarrow>
    ((rv1 s1 s2 kl b1 = Inl b1' \<longrightarrow>
      (b1'' \<in> F1set2 (s1 b1') \<longrightarrow>
        kl @ [Inl (tobd_F12 s1 b1' b1'')] \<in> Lev1 s1 s2 (Suc n) b1) \<and>
      (b2'' \<in> F1set3 (s1 b1') \<longrightarrow>
        kl @ [Inr (tobd_F13 s1 b1' b2'')] \<in> Lev1 s1 s2 (Suc n) b1)) \<and>
     (rv1 s1 s2 kl b1 = Inr b2' \<longrightarrow>
      (b1'' \<in> F2set2 (s2 b2') \<longrightarrow>
        kl @ [Inl (tobd_F22 s2 b2' b1'')] \<in> Lev1 s1 s2 (Suc n) b1) \<and>
      (b2'' \<in> F2set3 (s2 b2') \<longrightarrow>
        kl @ [Inr (tobd_F23 s2 b2' b2'')] \<in> Lev1 s1 s2 (Suc n) b1)))) \<and>
   (kl \<in> Lev2 s1 s2 n b2 \<longrightarrow>
    ((rv2 s1 s2 kl b2 = Inl b1' \<longrightarrow>
      (b1'' \<in> F1set2 (s1 b1') \<longrightarrow>
        kl @ [Inl (tobd_F12 s1 b1' b1'')] \<in> Lev2 s1 s2 (Suc n) b2) \<and>
      (b2'' \<in> F1set3 (s1 b1') \<longrightarrow>
        kl @ [Inr (tobd_F13 s1 b1' b2'')] \<in> Lev2 s1 s2 (Suc n) b2)) \<and>
     (rv2 s1 s2 kl b2 = Inr b2' \<longrightarrow>
      (b1'' \<in> F2set2 (s2 b2') \<longrightarrow>
        kl @ [Inl (tobd_F22 s2 b2' b1'')] \<in> Lev2 s1 s2 (Suc n) b2) \<and>
      (b2'' \<in> F2set3 (s2 b2') \<longrightarrow>
        kl @ [Inr (tobd_F23 s2 b2' b2'')] \<in> Lev2 s1 s2 (Suc n) b2))))"
  apply (rule nat_induct[of _ n])
    (*IB*)
   apply (rule allI)+
   apply (rule conjI)
    apply (rule impI)
    apply (drule subsetD[OF equalityD1[OF Lev1_0]])
    apply (erule singletonE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule rv1_Nil)
     apply (drule Inl_inject)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (rule conjI)
      apply (rule impI)
      apply (rule ssubst_mem[OF append_Nil])
      apply (rule subsetD[OF equalityD2])
       apply (rule Lev1_Suc)
      apply (rule UnI1)
      apply (rule CollectI)
      apply (rule exI)+
      apply (rule conjI)
       apply (rule refl)
      apply (erule conjI)
      apply (rule subsetD[OF equalityD2])
       apply (rule Lev1_0)
      apply (rule singletonI)
     apply (rule impI)
     apply (rule ssubst_mem[OF append_Nil])
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev1_Suc)
     apply (rule UnI2)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (erule conjI)
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev2_0)
     apply (rule singletonI)

    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule rv1_Nil)
    apply (erule notE[OF Inr_not_Inl])

   apply (rule impI)
   apply (drule rev_subsetD[OF _ equalityD1])
    apply (rule Lev2_0)
   apply (erule singletonE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule rv2_Nil)
    apply (erule notE[OF Inl_not_Inr])

   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule rv2_Nil)
   apply (drule Inr_inject)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm append_Nil} 1\<close>)+
   apply (rule conjI)
    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev2_Suc)
    apply (rule UnI1)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev1_0)
    apply (rule singletonI)
   apply (rule impI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_Suc)
   apply (rule UnI2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_0)
   apply (rule singletonI)

(*IS*)
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
      apply (rule subsetD[OF equalityD2])
       apply (rule Lev1_Suc)
      apply (rule ssubst_mem[OF append_Cons])
      apply (rule UnI1)
      apply (rule CollectI)
      apply (rule exI)+
      apply (rule conjI)
       apply (rule refl)
      apply (rule conjI)
       apply assumption
      apply (drule sym[OF trans[OF sym]])
       apply (rule trans[OF rv1_Cons])
       apply (rule trans[OF sum.case(1)])
       apply (erule arg_cong[OF frombd_F12_tobd_F12])
      apply (erule allE)+
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (erule mp)
      apply assumption

     apply (rule impI)
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev1_Suc)
     apply (rule ssubst_mem[OF append_Cons])
     apply (rule UnI1)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (rule conjI)
      apply assumption
     apply (drule sym[OF trans[OF sym]])
      apply (rule trans[OF rv1_Cons])
      apply (rule trans[OF sum.case(1)])
      apply (erule arg_cong[OF frombd_F12_tobd_F12])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (erule mp)
     apply assumption

    apply (rule impI)
    apply (rule conjI)
     apply (rule impI)
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev1_Suc)
     apply (rule ssubst_mem[OF append_Cons])
     apply (rule UnI1)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (rule conjI)
      apply assumption
     apply (drule sym[OF trans[OF sym]])
      apply (rule trans[OF rv1_Cons])
      apply (rule trans[OF sum.case(1)])
      apply (erule arg_cong[OF frombd_F12_tobd_F12])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule mp)
     apply assumption

    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev1_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI1)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (rule conjI)
     apply assumption
    apply (drule sym[OF trans[OF sym]])
     apply (rule trans[OF rv1_Cons])
     apply (rule trans[OF sum.case(1)])
     apply (erule arg_cong[OF frombd_F12_tobd_F12])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule mp)
    apply assumption
    (*UN1/2*)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm rv1_Cons} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm sum.case(2)} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm frombd_F13_tobd_F13} 1\<close>)
    apply assumption
   apply (rule conjI)
    apply (rule impI)
    apply (rule conjI)
     apply (rule impI)
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev1_Suc)
     apply (rule ssubst_mem[OF append_Cons])
     apply (rule UnI2)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (erule conjI)
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule mp)
     apply assumption

    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev1_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI2)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (rule impI)
   apply (rule conjI)
    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev1_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI2)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (rule impI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev1_Suc)
   apply (rule ssubst_mem[OF append_Cons])
   apply (rule UnI2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply assumption

(**)

  apply (rule impI)
  apply (drule rev_subsetD[OF _ equalityD1])
   apply (rule Lev2_Suc)
  apply (erule UnE)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm rv2_Cons} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm sum.case(1)} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm frombd_F22_tobd_F22} 1\<close>)
    apply assumption
   apply (rule conjI)
    apply (rule impI)
    apply (rule conjI)
     apply (rule impI)
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev2_Suc)
     apply (rule ssubst_mem[OF append_Cons])
     apply (rule UnI1)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (erule conjI)
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule mp)
     apply assumption

    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev2_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI1)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (rule impI)
   apply (rule conjI)
    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev2_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI1)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (rule impI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_Suc)
   apply (rule ssubst_mem[OF append_Cons])
   apply (rule UnI1)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply assumption
    (*UN1/2*)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (tactic \<open>stac @{context} @{thm rv2_Cons} 1\<close>)
  apply (tactic \<open>stac @{context} @{thm sum.case(2)} 1\<close>)
  apply (tactic \<open>stac @{context} @{thm frombd_F23_tobd_F23} 1\<close>)
   apply assumption
  apply (rule conjI)
   apply (rule impI)
   apply (rule conjI)
    apply (rule impI)
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev2_Suc)
    apply (rule ssubst_mem[OF append_Cons])
    apply (rule UnI2)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply assumption

   apply (rule impI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_Suc)
   apply (rule ssubst_mem[OF append_Cons])
   apply (rule UnI2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply assumption

  apply (rule impI)
  apply (rule conjI)
   apply (rule impI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_Suc)
   apply (rule ssubst_mem[OF append_Cons])
   apply (rule UnI2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule mp)
   apply assumption

  apply (rule impI)
  apply (rule subsetD[OF equalityD2])
   apply (rule Lev2_Suc)
  apply (rule ssubst_mem[OF append_Cons])
  apply (rule UnI2)
  apply (rule CollectI)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule refl)
  apply (erule conjI)
  apply (erule allE)+
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (drule mp)
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (drule mp)
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule mp)
  apply assumption
  done

lemmas Fset_Lev' = spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF Fset_Lev]]]]]]]
lemmas F1set2_Lev1 = mp[OF conjunct1[OF mp[OF conjunct1[OF mp[OF conjunct1[OF Fset_Lev']]]]]]
lemmas F1set2_Lev2 = mp[OF conjunct1[OF mp[OF conjunct1[OF mp[OF conjunct2[OF Fset_Lev']]]]]]
lemmas F2set2_Lev1 = mp[OF conjunct1[OF mp[OF conjunct2[OF mp[OF conjunct1[OF Fset_Lev']]]]]]
lemmas F2set2_Lev2 = mp[OF conjunct1[OF mp[OF conjunct2[OF mp[OF conjunct2[OF Fset_Lev']]]]]]
lemmas F1set3_Lev1 = mp[OF conjunct2[OF mp[OF conjunct1[OF mp[OF conjunct1[OF Fset_Lev']]]]]]
lemmas F1set3_Lev2 = mp[OF conjunct2[OF mp[OF conjunct1[OF mp[OF conjunct2[OF Fset_Lev']]]]]]
lemmas F2set3_Lev1 = mp[OF conjunct2[OF mp[OF conjunct2[OF mp[OF conjunct1[OF Fset_Lev']]]]]]
lemmas F2set3_Lev2 = mp[OF conjunct2[OF mp[OF conjunct2[OF mp[OF conjunct2[OF Fset_Lev']]]]]]

lemma Fset_image_Lev:
  "\<forall>kl k b1 b2 b1' b2'.
   (kl \<in> Lev1 s1 s2 n b1 \<longrightarrow>
    (kl @ [Inl k] \<in> Lev1 s1 s2 (Suc n) b1 \<longrightarrow>
      (rv1 s1 s2 kl b1 = Inl b1' \<longrightarrow> k \<in> tobd_F12 s1 b1' ` F1set2 (s1 b1')) \<and>
      (rv1 s1 s2 kl b1 = Inr b2' \<longrightarrow> k \<in> tobd_F22 s2 b2' ` F2set2 (s2 b2'))) \<and>
    (kl @ [Inr k] \<in> Lev1 s1 s2 (Suc n) b1 \<longrightarrow>
      (rv1 s1 s2 kl b1 = Inl b1' \<longrightarrow> k \<in> tobd_F13 s1 b1' ` F1set3 (s1 b1')) \<and>
      (rv1 s1 s2 kl b1 = Inr b2' \<longrightarrow> k \<in> tobd_F23 s2 b2' ` F2set3 (s2 b2')))) \<and>
   (kl \<in> Lev2 s1 s2 n b2 \<longrightarrow>
    (kl @ [Inl k] \<in> Lev2 s1 s2 (Suc n) b2 \<longrightarrow>
      (rv2 s1 s2 kl b2 = Inl b1' \<longrightarrow> k \<in> tobd_F12 s1 b1' ` F1set2 (s1 b1')) \<and>
      (rv2 s1 s2 kl b2 = Inr b2' \<longrightarrow> k \<in> tobd_F22 s2 b2' ` F2set2 (s2 b2'))) \<and>
    (kl @ [Inr k] \<in> Lev2 s1 s2 (Suc n) b2 \<longrightarrow>
      (rv2 s1 s2 kl b2 = Inl b1' \<longrightarrow> k \<in> tobd_F13 s1 b1' ` F1set3 (s1 b1')) \<and>
      (rv2 s1 s2 kl b2 = Inr b2' \<longrightarrow> k \<in> tobd_F23 s2 b2' ` F2set3 (s2 b2'))))"
  apply (rule nat_induct[of _ n])
    (*IB*)
   apply (rule allI)+
   apply (rule conjI)
    apply (rule impI)
    apply (drule subsetD[OF equalityD1[OF Lev1_0]])
    apply (erule singletonE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
      apply (drule trans[OF sym])
       apply (rule rv1_Nil)
      apply (drule ssubst_mem[OF sym[OF append_Nil]])
      apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
      apply (drule Inl_inject)
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (erule UnE)
       apply (erule CollectE exE conjE)+
       apply (drule list.inject[THEN iffD1])
       apply (erule conjE)
       apply (drule Inl_inject)
       apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
       apply (erule imageI)
      apply (erule CollectE exE conjE)+
      apply (drule list.inject[THEN iffD1])
      apply (erule conjE)
      apply (erule notE[OF Inl_not_Inr])
     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule rv1_Nil)
     apply (erule notE[OF Inr_not_Inl])

    apply (rule impI)
    apply (rule conjI)
     apply (rule impI)
     apply (drule ssubst_mem[OF sym[OF append_Nil]])
     apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
     apply (drule trans[OF sym])
      apply (rule rv1_Nil)
     apply (drule Inl_inject)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (erule UnE)
      apply (erule CollectE exE conjE)+
      apply (drule list.inject[THEN iffD1])
      apply (erule conjE)
      apply (erule notE[OF Inr_not_Inl])
     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (drule Inr_inject)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (erule imageI)
    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule rv1_Nil)
    apply (erule notE[OF Inr_not_Inl])

   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev2_0]])
   apply (erule singletonE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (rule conjI)
     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule rv2_Nil)
     apply (erule notE[OF Inl_not_Inr])
    apply (rule impI)
    apply (drule ssubst_mem[OF sym[OF append_Nil]])
    apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
    apply (drule trans[OF sym])
     apply (rule rv2_Nil)
    apply (drule Inr_inject)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (erule UnE)
     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (drule Inl_inject)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (erule imageI)
    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inl_not_Inr])

   apply (rule impI)
   apply (rule conjI)
    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule rv2_Nil)
    apply (erule notE[OF Inl_not_Inr])
   apply (rule impI)
   apply (drule ssubst_mem[OF sym[OF append_Nil]])
   apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
   apply (drule trans[OF sym])
    apply (rule rv2_Nil)
   apply (drule Inr_inject)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inr_not_Inl])
   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (drule Inr_inject)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule imageI)

(*IS*)

  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (drule ssubst_mem[OF sym[OF append_Cons]])
     apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
     apply (erule UnE)
      apply (erule CollectE exE conjE)+
      apply (drule list.inject[THEN iffD1])
      apply (erule conjE)
      apply (drule Inl_inject)
      apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 (@{thm tobd_F12_inj} RS iffD1)) 1\<close>)
        apply assumption
       apply assumption
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (rule conjI)
       apply (rule impI)
       apply (drule trans[OF sym])
        apply (rule trans[OF rv1_Cons])
        apply (rule trans[OF arg_cong[OF sum.case(1)]])
        apply (erule arg_cong[OF frombd_F12_tobd_F12])
       apply (erule allE)+
       apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
       apply (drule mp)
        apply assumption
       apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
       apply (drule mp)
        apply assumption
       apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
       apply (erule mp)
       apply (erule sym)

      apply (rule impI)
      apply (drule trans[OF sym])
       apply (rule trans[OF rv1_Cons])
       apply (rule trans[OF arg_cong[OF sum.case(1)]])
       apply (erule arg_cong[OF frombd_F12_tobd_F12])
      apply (erule allE)+
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
      apply (erule mp)
      apply (erule sym)

     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (erule notE[OF Inl_not_Inr])

    apply (rule impI)
    apply (drule ssubst_mem[OF sym[OF append_Cons]])
    apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
    apply (erule UnE)
     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (drule Inl_inject)
     apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F12_inj[THEN iffD1]}) 1\<close>)
       apply assumption
      apply assumption
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (rule conjI)
      apply (rule impI)
      apply (drule trans[OF sym])
       apply (rule trans[OF rv1_Cons])
       apply (rule trans[OF arg_cong[OF sum.case(1)]])
       apply (erule arg_cong[OF frombd_F12_tobd_F12])
      apply (erule allE)+
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (erule mp)
      apply (erule sym)

     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule trans[OF rv1_Cons])
      apply (rule trans[OF arg_cong[OF sum.case(1)]])
      apply (erule arg_cong[OF frombd_F12_tobd_F12])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (erule mp)
     apply (erule sym)

    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inl_not_Inr])
    (*outer UN1/2*)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (drule ssubst_mem[OF sym[OF append_Cons]])
    apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
    apply (erule UnE)
     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (erule notE[OF Inr_not_Inl])

    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (drule Inr_inject)
    apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F13_inj[THEN iffD1]}) 1\<close>)
      apply assumption
     apply assumption
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule trans[OF rv1_Cons])
      apply (rule trans[OF arg_cong[OF sum.case(2)]])
      apply (erule arg_cong[OF frombd_F13_tobd_F13])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule mp)
     apply (erule sym)

    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule trans[OF rv1_Cons])
     apply (rule trans[OF arg_cong[OF sum.case(2)]])
     apply (erule arg_cong[OF frombd_F13_tobd_F13])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule mp)
    apply (erule sym)

   apply (rule impI)
   apply (drule ssubst_mem[OF sym[OF append_Cons]])
   apply (drule subsetD[OF equalityD1[OF Lev1_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inr_not_Inl])

   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (drule Inr_inject)
   apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F13_inj[THEN iffD1]}) 1\<close>)
     apply assumption
    apply assumption
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule trans[OF rv1_Cons])
     apply (rule trans[OF arg_cong[OF sum.case(2)]])
     apply (erule arg_cong[OF frombd_F13_tobd_F13])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply (erule sym)

   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule trans[OF rv1_Cons])
    apply (rule trans[OF arg_cong[OF sum.case(2)]])
    apply (erule arg_cong[OF frombd_F13_tobd_F13])
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply (erule sym)

(*1/2*)

  apply (rule impI)
  apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
  apply (erule UnE)
   apply (erule CollectE exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (drule ssubst_mem[OF sym[OF append_Cons]])
    apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
    apply (erule UnE)
     apply (erule CollectE exE conjE)+
     apply (drule list.inject[THEN iffD1])
     apply (erule conjE)
     apply (drule Inl_inject)
     apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F22_inj[THEN iffD1]}) 1\<close>)
       apply assumption
      apply assumption
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (rule conjI)
      apply (rule impI)
      apply (drule trans[OF sym])
       apply (rule trans[OF rv2_Cons])
       apply (rule trans[OF arg_cong[OF sum.case(1)]])
       apply (erule arg_cong[OF frombd_F22_tobd_F22])
      apply (erule allE)+
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (drule mp)
       apply assumption
      apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (erule mp)
      apply (erule sym)

     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule trans[OF rv2_Cons])
      apply (rule trans[OF arg_cong[OF sum.case(1)]])
      apply (erule arg_cong[OF frombd_F22_tobd_F22])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (erule mp)
     apply (erule sym)

    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inl_not_Inr])

   apply (rule impI)
   apply (drule ssubst_mem[OF sym[OF append_Cons]])
   apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (drule Inl_inject)
    apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F22_inj[THEN iffD1]}) 1\<close>)
      apply assumption
     apply assumption
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
     apply (rule impI)
     apply (drule trans[OF sym])
      apply (rule trans[OF rv2_Cons])
      apply (rule trans[OF arg_cong[OF sum.case(1)]])
      apply (erule arg_cong[OF frombd_F22_tobd_F22])
     apply (erule allE)+
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (drule mp)
      apply assumption
     apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (erule mp)
     apply (erule sym)

    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule trans[OF rv2_Cons])
     apply (rule trans[OF arg_cong[OF sum.case(1)]])
     apply (erule arg_cong[OF frombd_F22_tobd_F22])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (erule mp)
    apply (erule sym)

   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (erule notE[OF Inl_not_Inr])
    (*outer UN1/2*)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule conjI)
   apply (rule impI)
   apply (drule ssubst_mem[OF sym[OF append_Cons]])
   apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
   apply (erule UnE)
    apply (erule CollectE exE conjE)+
    apply (drule list.inject[THEN iffD1])
    apply (erule conjE)
    apply (erule notE[OF Inr_not_Inl])

   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (drule Inr_inject)
   apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F23_inj[THEN iffD1]}) 1\<close>)
     apply assumption
    apply assumption
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule conjI)
    apply (rule impI)
    apply (drule trans[OF sym])
     apply (rule trans[OF rv2_Cons])
     apply (rule trans[OF arg_cong[OF sum.case(2)]])
     apply (erule arg_cong[OF frombd_F23_tobd_F23])
    apply (erule allE)+
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (drule mp)
     apply assumption
    apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
    apply (erule mp)
    apply (erule sym)

   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule trans[OF rv2_Cons])
    apply (rule trans[OF arg_cong[OF sum.case(2)]])
    apply (erule arg_cong[OF frombd_F23_tobd_F23])
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (erule mp)
   apply (erule sym)

  apply (rule impI)
  apply (drule ssubst_mem[OF sym[OF append_Cons]])
  apply (drule subsetD[OF equalityD1[OF Lev2_Suc]])
  apply (erule UnE)
   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (erule notE[OF Inr_not_Inl])

  apply (erule CollectE exE conjE)+
  apply (drule list.inject[THEN iffD1])
  apply (erule conjE)
  apply (drule Inr_inject)
  apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F23_inj[THEN iffD1]}) 1\<close>)
    apply assumption
   apply assumption
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule conjI)
   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule trans[OF rv2_Cons])
    apply (rule trans[OF arg_cong[OF sum.case(2)]])
    apply (erule arg_cong[OF frombd_F23_tobd_F23])
   apply (erule allE)+
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (drule mp)
    apply assumption
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule mp)
   apply (erule sym)

  apply (rule impI)
  apply (drule trans[OF sym])
   apply (rule trans[OF rv2_Cons])
   apply (rule trans[OF arg_cong[OF sum.case(2)]])
   apply (erule arg_cong[OF frombd_F23_tobd_F23])
  apply (erule allE)+
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (drule mp)
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (drule mp)
   apply assumption
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule mp)
  apply (erule sym)
  done

lemmas Fset_image_Lev' =
  spec[OF spec[OF spec[OF  spec[OF spec[OF spec[OF Fset_image_Lev]]]]]]
lemmas F1set2_image_Lev1 =
  mp[OF conjunct1[OF mp[OF conjunct1[OF mp[OF conjunct1[OF Fset_image_Lev']]]]]]
lemmas F1set2_image_Lev2 =
  mp[OF conjunct1[OF mp[OF conjunct1[OF mp[OF conjunct2[OF Fset_image_Lev']]]]]]
lemmas F1set3_image_Lev1 =
  mp[OF conjunct1[OF mp[OF conjunct2[OF mp[OF conjunct1[OF Fset_image_Lev']]]]]]
lemmas F1set3_image_Lev2 =
  mp[OF conjunct1[OF mp[OF conjunct2[OF mp[OF conjunct2[OF Fset_image_Lev']]]]]]
lemmas F2set2_image_Lev1 =
  mp[OF conjunct2[OF mp[OF conjunct1[OF mp[OF conjunct1[OF Fset_image_Lev']]]]]]
lemmas F2set2_image_Lev2 =
  mp[OF conjunct2[OF mp[OF conjunct1[OF mp[OF conjunct2[OF Fset_image_Lev']]]]]]
lemmas F2set3_image_Lev1 =
  mp[OF conjunct2[OF mp[OF conjunct2[OF mp[OF conjunct1[OF Fset_image_Lev']]]]]]
lemmas F2set3_image_Lev2 =
  mp[OF conjunct2[OF mp[OF conjunct2[OF mp[OF conjunct2[OF Fset_image_Lev']]]]]]

lemma mor_beh:
  "mor UNIV UNIV s1 s2 carT1 carT2 strT1 strT2 (beh1 s1 s2) (beh2 s1 s2)"
  apply (rule mor_cong)
    apply (rule ext[OF beh1_def])
   apply (rule ext[OF beh2_def])
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule subsetD[OF equalityD2[OF carT1_def]])
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (rule conjI)
     apply (rule conjI)
      apply (rule UN_I)
       apply (rule UNIV_I)
      apply (rule subsetD)
       apply (rule equalityD2)
       apply (rule Lev1_0)
      apply (rule singletonI)

     apply (rule ballI)
     apply (erule UN_E)
     apply (rule conjI)
      apply (rule ballI)
      apply (erule CollectE SuccD[elim_format] UN_E)+
      apply (rule rev_mp[OF rv1_Inl_last impI])
      apply (erule exE)
      apply (rule iffD2[OF isNode1_def])
      apply (rule exI)
      apply (rule conjI)
       apply (erule trans[OF sum.case_cong_weak])
       apply (rule sum.case(1))

      apply (rule conjI)
       apply (rule trans[OF F1.set_map(2)])
       apply (rule equalityI)
        apply (rule image_subsetI)
        apply (rule CollectI)
        apply (rule SuccI)
        apply (rule UN_I[OF UNIV_I])
        apply (erule F1set2_Lev1)
         apply assumption
        apply assumption
       apply (rule subsetI)
       apply (erule CollectE SuccD[elim_format] UN_E)+
       apply (erule thin_rl)
       apply (erule thin_rl)
       apply (erule thin_rl)
       apply (erule thin_rl)
       apply (rule F1set2_image_Lev1)
         apply assumption
        apply (drule length_Lev1)
        apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
        apply (drule length_Lev1')
        apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
       apply assumption

      apply (rule trans[OF F1.set_map(3)])
      apply (rule equalityI)
       apply (rule image_subsetI)
       apply (rule CollectI)
       apply (rule SuccI)
       apply (rule UN_I[OF UNIV_I])
       apply (erule F1set3_Lev1)
        apply assumption
       apply assumption
      apply (rule subsetI)
      apply (erule CollectE SuccD[elim_format] UN_E)+
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (rule F1set3_image_Lev1)
        apply assumption
       apply (drule length_Lev1)
       apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
       apply (drule length_Lev1')
       apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
      apply assumption

     apply (rule ballI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (rule rev_mp[OF rv1_Inr_last impI])
     apply (erule exE)
     apply (rule iffD2[OF isNode2_def])
     apply (rule exI)
     apply (rule conjI)
      apply (erule trans[OF sum.case_cong_weak])
      apply (rule sum.case(2))

     apply (rule conjI)
      apply (rule trans[OF F2.set_map(2)])
      apply (rule equalityI)
       apply (rule image_subsetI)
       apply (rule CollectI)
       apply (rule SuccI)
       apply (rule UN_I[OF UNIV_I])
       apply (erule F2set2_Lev1)
        apply assumption
       apply assumption
      apply (rule subsetI)
      apply (erule CollectE SuccD[elim_format] UN_E)+
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (rule F2set2_image_Lev1)
        apply assumption
       apply (drule length_Lev1)
       apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
       apply (drule length_Lev1')
       apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
      apply assumption

     apply (rule trans[OF F2.set_map(3)])
     apply (rule equalityI)
      apply (rule image_subsetI)
      apply (rule CollectI)
      apply (rule SuccI)
      apply (rule UN_I[OF UNIV_I])
      apply (erule F2set3_Lev1)
       apply assumption
      apply assumption
     apply (rule subsetI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (rule F2set3_image_Lev1)
       apply assumption
      apply (drule length_Lev1)
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (drule length_Lev1')
      apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
     apply assumption

    apply (rule iffD2[OF isNode1_def])
    apply (rule exI)
    apply (rule conjI)
     apply (rule trans[OF sum.case_cong_weak])
      apply (rule rv1_Nil)
     apply (rule sum.case(1))

    apply (rule conjI)
     apply (rule trans[OF F1.set_map(2)])
     apply (rule equalityI)
      apply (rule image_subsetI)
      apply (rule CollectI)
      apply (rule SuccI)
      apply (rule UN_I[OF UNIV_I])
      apply (rule F1set2_Lev1)
        apply (rule subsetD[OF equalityD2])
         apply (rule Lev1_0)
        apply (rule singletonI)
       apply (rule rv1_Nil)
      apply assumption
     apply (rule subsetI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (rule F1set2_image_Lev1)
       apply (rule subsetD[OF equalityD2[OF Lev1_0]])
       apply (rule singletonI)
      apply (drule length_Lev1')
      apply (erule subsetD[OF equalityD1[OF arg_cong[OF
            trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]])
     apply (rule rv1_Nil)

    apply (rule trans[OF F1.set_map(3)])
    apply (rule equalityI)
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule SuccI)
     apply (rule UN_I[OF UNIV_I])
     apply (rule F1set3_Lev1)
       apply (rule subsetD[OF equalityD2])
        apply (rule Lev1_0)
       apply (rule singletonI)
      apply (rule rv1_Nil)
     apply assumption
    apply (rule subsetI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (rule F1set3_image_Lev1)
      apply (rule subsetD[OF equalityD2[OF Lev1_0]])
      apply (rule singletonI)
     apply (drule length_Lev1')
     apply (erule subsetD[OF equalityD1[OF arg_cong[OF
            trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]])
    apply (rule rv1_Nil)

(**)

   apply (rule ballI)
   apply (rule subsetD[OF equalityD2[OF carT2_def]])
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule conjI)
    apply (rule conjI)
     apply (rule UN_I)
      apply (rule UNIV_I)
     apply (rule subsetD)
      apply (rule equalityD2)
      apply (rule Lev2_0)
     apply (rule singletonI)

    apply (rule ballI)
    apply (erule UN_E)
    apply (rule conjI)
     apply (rule ballI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (rule rev_mp[OF rv2_Inl_last impI])
     apply (erule exE)
     apply (rule iffD2[OF isNode1_def])
     apply (rule exI)
     apply (rule conjI)
      apply (erule trans[OF sum.case_cong_weak])
      apply (rule sum.case(1))

     apply (rule conjI)
      apply (rule trans[OF F1.set_map(2)])
      apply (rule equalityI)
       apply (rule image_subsetI)
       apply (rule CollectI)
       apply (rule SuccI)
       apply (rule UN_I[OF UNIV_I])
       apply (erule F1set2_Lev2)
        apply assumption
       apply assumption
      apply (rule subsetI)
      apply (erule CollectE SuccD[elim_format] UN_E)+
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (rule F1set2_image_Lev2)
        apply assumption
       apply (drule length_Lev2)
       apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
       apply (drule length_Lev2')
       apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
      apply assumption

     apply (rule trans[OF F1.set_map(3)])
     apply (rule equalityI)
      apply (rule image_subsetI)
      apply (rule CollectI)
      apply (rule SuccI)
      apply (rule UN_I[OF UNIV_I])
      apply (erule F1set3_Lev2)
       apply assumption
      apply assumption
     apply (rule subsetI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (rule F1set3_image_Lev2)
       apply assumption
      apply (drule length_Lev2)
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (drule length_Lev2')
      apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
     apply assumption

    apply (rule ballI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (rule rev_mp[OF rv2_Inr_last impI])
    apply (erule exE)
    apply (rule iffD2[OF isNode2_def])
    apply (rule exI)
    apply (rule conjI)
     apply (erule trans[OF sum.case_cong_weak])
     apply (rule sum.case(2))

    apply (rule conjI)
     apply (rule trans[OF F2.set_map(2)])
     apply (rule equalityI)
      apply (rule image_subsetI)
      apply (rule CollectI)
      apply (rule SuccI)
      apply (rule UN_I[OF UNIV_I])
      apply (erule F2set2_Lev2)
       apply assumption
      apply assumption
     apply (rule subsetI)
     apply (erule CollectE SuccD[elim_format] UN_E)+
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (erule thin_rl)
     apply (rule F2set2_image_Lev2)
       apply assumption
      apply (drule length_Lev2)
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (drule length_Lev2')
      apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
     apply assumption

    apply (rule trans[OF F2.set_map(3)])
    apply (rule equalityI)
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule SuccI)
     apply (rule UN_I[OF UNIV_I])
     apply (erule F2set3_Lev2)
      apply assumption
     apply assumption
    apply (rule subsetI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (rule F2set3_image_Lev2)
      apply assumption
     apply (drule length_Lev2)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (drule length_Lev2')
     apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
    apply assumption

   apply (rule iffD2[OF isNode2_def])
   apply (rule exI)
   apply (rule conjI)
    apply (rule trans[OF sum.case_cong_weak])
     apply (rule rv2_Nil)
    apply (rule sum.case(2))

   apply (rule conjI)
    apply (rule trans[OF F2.set_map(2)])
    apply (rule equalityI)
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule SuccI)
     apply (rule UN_I[OF UNIV_I])
     apply (rule F2set2_Lev2)
       apply (rule subsetD[OF equalityD2[OF Lev2_0]])
       apply (rule singletonI)
      apply (rule rv2_Nil)
     apply assumption
    apply (rule subsetI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (rule F2set2_image_Lev2)
      apply (rule subsetD[OF equalityD2[OF Lev2_0]])
      apply (rule singletonI)
     apply (drule length_Lev2')
     apply (erule subsetD[OF equalityD1[OF arg_cong[OF
            trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]])
    apply (rule rv2_Nil)

   apply (rule trans[OF F2.set_map(3)])
   apply (rule equalityI)
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule SuccI)
    apply (rule UN_I[OF UNIV_I])
    apply (rule F2set3_Lev2)
      apply (rule subsetD[OF equalityD2])
       apply (rule Lev2_0)
      apply (rule singletonI)
     apply (rule rv2_Nil)
    apply assumption
   apply (rule subsetI)
   apply (erule CollectE SuccD[elim_format] UN_E)+
   apply (rule F2set3_image_Lev2)
     apply (rule subsetD[OF equalityD2[OF Lev2_0]])
     apply (rule singletonI)
    apply (drule length_Lev2')
    apply (erule subsetD[OF equalityD1[OF arg_cong[OF
            trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]])
   apply (rule rv2_Nil)

(*mor_tac*)

  apply (rule conjI)
   apply (rule ballI)
   apply (rule sym)
   apply (rule trans)
    apply (rule trans[OF fun_cong[OF strT1_def] prod.case])
   apply (tactic \<open>CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (@{thm rv1_Nil} RS eq_reflection)))) @{context}) 1\<close>)
   apply (rule trans[OF sum.case_cong_weak])
    apply (rule sum.case(1))
   apply (rule trans[OF sum.case(1)])
   apply (rule trans[OF F1map_comp_id])
   apply (rule F1.map_cong0[OF refl])
    apply (rule trans)
     apply (rule o_apply)
    apply (rule iffD2)
     apply (rule prod.inject)
    apply (rule conjI)
     apply (rule trans)
      apply (rule Shift_def)

(*UN_Lev*)
     apply (rule equalityI)
      apply (rule subsetI)
      apply (erule thin_rl)
      apply (erule CollectE UN_E)+
      apply (drule length_Lev1')
      apply (drule asm_rl)
      apply (erule thin_rl)
      apply (drule rev_subsetD[OF _ equalityD1])
       apply (rule trans[OF arg_cong[OF length_Cons]])
       apply (rule Lev1_Suc)
      apply (erule UnE)
       apply (erule CollectE exE conjE)+
       apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
       apply (erule conjE)
       apply (drule Inl_inject)
       apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F12_inj[THEN iffD1]}) 1\<close>)
         apply assumption
        apply assumption
       apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
       apply (erule UN_I[OF UNIV_I])
      apply (erule CollectE exE conjE)+
      apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
      apply (erule conjE)
      apply (erule notE[OF Inl_not_Inr])

     apply (rule UN_least)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (rule UN_I[OF UNIV_I])
     apply (rule subsetD[OF equalityD2])
      apply (rule Lev1_Suc)
     apply (rule UnI1)
     apply (rule CollectI)
     apply (rule exI)+
     apply (rule conjI)
      apply (rule refl)
     apply (erule conjI)
     apply assumption
    (**)

    apply (rule trans)
     apply (rule shift_def)
    apply (rule iffD2)
     apply (rule fun_eq_iff)
    apply (rule allI)
    apply (tactic \<open>CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (@{thm rv1_Cons} RS eq_reflection)))) @{context}) 1\<close>)
    apply (rule sum.case_cong_weak)
    apply (rule trans[OF sum.case(1)])
    apply (drule frombd_F12_tobd_F12)
    apply (erule arg_cong)

   apply (rule trans)
    apply (rule o_apply)
   apply (rule iffD2)
    apply (rule prod.inject)
   apply (rule conjI)
    apply (rule trans)
     apply (rule Shift_def)

(*UN_Lev*)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (erule thin_rl)
     apply (erule CollectE UN_E)+
     apply (drule length_Lev1')
     apply (drule asm_rl)
     apply (erule thin_rl)
     apply (drule rev_subsetD[OF _ equalityD1])
      apply (rule trans[OF arg_cong[OF length_Cons]])
      apply (rule Lev1_Suc)
     apply (erule UnE)
      apply (erule CollectE exE conjE)+
      apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
      apply (erule conjE)
      apply (erule notE[OF Inr_not_Inl])
     apply (erule CollectE exE conjE)+
     apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
     apply (erule conjE)
     apply (drule Inr_inject)
     apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F13_inj[THEN iffD1]}) 1\<close>)
       apply assumption
      apply assumption
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (erule UN_I[OF UNIV_I])

    apply (rule UN_least)
    apply (rule subsetI)
    apply (rule CollectI)
    apply (rule UN_I[OF UNIV_I])
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev1_Suc)
    apply (rule UnI2)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply assumption
    (**)

   apply (rule trans)
    apply (rule shift_def)
   apply (rule iffD2)
    apply (rule fun_eq_iff)
   apply (rule allI)
   apply (rule sum.case_cong_weak)
   apply (rule trans[OF rv1_Cons])
   apply (rule trans[OF sum.case(2)])
   apply (erule arg_cong[OF frombd_F13_tobd_F13])

(**)

  apply (rule ballI)
  apply (rule sym)
  apply (rule trans)
   apply (rule trans[OF fun_cong[OF strT2_def] prod.case])
  apply (rule trans[OF sum.case_cong_weak[OF trans[OF sum.case_cong_weak]]])
    apply (rule rv2_Nil)
   apply (rule sum.case(2))
  apply (rule trans[OF sum.case(2)])
  apply (rule trans[OF F2map_comp_id])
  apply (rule F2.map_cong0[OF refl])
   apply (rule trans)
    apply (rule o_apply)
   apply (rule iffD2)
    apply (rule prod.inject)
   apply (rule conjI)
    apply (rule trans)
     apply (rule Shift_def)

(*UN_Lev*)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (erule thin_rl)
     apply (erule CollectE UN_E)+
     apply (drule length_Lev2')
     apply (drule asm_rl)
     apply (erule thin_rl)
     apply (drule rev_subsetD[OF _ equalityD1])
      apply (rule trans[OF arg_cong[OF length_Cons]])
      apply (rule Lev2_Suc)
     apply (erule UnE)
      apply (erule CollectE exE conjE)+
      apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
      apply (erule conjE)
      apply (drule Inl_inject)
      apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F22_inj[THEN iffD1]}) 1\<close>)
        apply assumption
       apply assumption
      apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
      apply (erule UN_I[OF UNIV_I])
     apply (erule CollectE exE conjE)+
     apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
     apply (erule conjE)
     apply (erule notE[OF Inl_not_Inr])

    apply (rule UN_least)
    apply (rule subsetI)
    apply (rule CollectI)
    apply (rule UN_I[OF UNIV_I])
    apply (rule subsetD[OF equalityD2])
     apply (rule Lev2_Suc)
    apply (rule UnI1)
    apply (rule CollectI)
    apply (rule exI)+
    apply (rule conjI)
     apply (rule refl)
    apply (erule conjI)
    apply assumption
    (**)

   apply (rule trans)
    apply (rule shift_def)
   apply (rule iffD2)
    apply (rule fun_eq_iff)
   apply (rule allI)
   apply (rule sum.case_cong_weak)
   apply (rule trans[OF rv2_Cons])
   apply (rule trans[OF arg_cong[OF sum.case(1)]])
   apply (erule arg_cong[OF frombd_F22_tobd_F22])

  apply (rule trans)
   apply (rule o_apply)
  apply (rule iffD2)
   apply (rule prod.inject)
  apply (rule conjI)
   apply (rule trans)
    apply (rule Shift_def)

(*UN_Lev*)
   apply (rule equalityI)
    apply (rule subsetI)
    apply (erule thin_rl)
    apply (erule CollectE UN_E)+
    apply (drule length_Lev2')
    apply (drule asm_rl)
    apply (erule thin_rl)
    apply (drule rev_subsetD[OF _ equalityD1])
     apply (rule trans[OF arg_cong[OF length_Cons]])
     apply (rule Lev2_Suc)
    apply (erule UnE)
     apply (erule CollectE exE conjE)+
     apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
     apply (erule conjE)
     apply (erule notE[OF Inr_not_Inl])
    apply (erule CollectE exE conjE)+
    apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
    apply (erule conjE)
    apply (drule Inr_inject)
    apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_F23_inj[THEN iffD1]}) 1\<close>)
      apply assumption
     apply assumption
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (erule UN_I[OF UNIV_I])

   apply (rule UN_least)
   apply (rule subsetI)
   apply (rule CollectI)
   apply (rule UN_I[OF UNIV_I])
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev2_Suc)
   apply (rule UnI2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply assumption
    (**)

  apply (rule trans)
   apply (rule shift_def)
  apply (rule iffD2)
   apply (rule fun_eq_iff)
  apply (rule allI)

  apply (rule sum.case_cong_weak)
  apply (rule trans[OF rv2_Cons])
  apply (rule trans[OF arg_cong[OF sum.case(2)]])
  apply (erule arg_cong[OF frombd_F23_tobd_F23])
  done

subsection \<open>Quotient Coalgebra\<close>

(* final coalgebra *)
abbreviation car_final1 where
  "car_final1 \<equiv> carT1 // (lsbis1 carT1 carT2 strT1 strT2)"
abbreviation car_final2 where
  "car_final2 \<equiv> carT2 // (lsbis2 carT1 carT2 strT1 strT2)"
abbreviation str_final1 where
  "str_final1 \<equiv> univ (F1map id
    (Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2))
    (Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2)) o strT1)"
abbreviation str_final2 where
  "str_final2 \<equiv> univ (F2map id
    (Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2))
    (Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2)) o strT2)"

lemma congruent_strQ1: "congruent (lsbis1 carT1 carT2 strT1 strT2 :: 'a carrier rel)
  (F1map id (Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2 :: 'a carrier rel))
            (Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2 :: 'a carrier rel)) o strT1)"
  apply (rule congruentI)
  apply (drule lsbisE1)
  apply (erule bexE conjE CollectE)+
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule trans[OF F1map_comp_id])
  apply (rule trans[OF F1.map_cong0])
     apply (rule refl)
    apply (rule equiv_proj)
     apply (rule equiv_lsbis1)
     apply (rule coalg_T)
    apply (erule subsetD)
    apply assumption
   apply (rule equiv_proj)
    apply (rule equiv_lsbis2)
    apply (rule coalg_T)
   apply (erule subsetD)
   apply assumption
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule F1map_comp_id)
  done

lemma congruent_strQ2: "congruent (lsbis2 carT1 carT2 strT1 strT2 :: 'a carrier rel)
  (F2map id (Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2 :: 'a carrier rel))
            (Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2 :: 'a carrier rel)) o strT2)"
  apply (rule congruentI)
  apply (drule lsbisE2)
  apply (erule bexE conjE CollectE)+
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule trans[OF F2map_comp_id])
  apply (rule trans[OF F2.map_cong0])
     apply (rule refl)
    apply (rule equiv_proj)
     apply (rule equiv_lsbis1)
     apply (rule coalg_T)
    apply (erule subsetD)
    apply assumption
   apply (rule equiv_proj)
    apply (rule equiv_lsbis2)
    apply (rule coalg_T)
   apply (erule subsetD)
   apply assumption
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule F2map_comp_id)
  done

lemma coalg_final:
  "coalg car_final1 car_final2 str_final1 str_final2"
  apply (tactic \<open>rtac @{context} (@{thm coalg_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule univ_preserves)
     apply (rule equiv_lsbis1)
     apply (rule coalg_T)
    apply (rule congruent_strQ1)
   apply (rule ballI)
   apply (rule ssubst_mem)
    apply (rule o_apply)
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule subset_UNIV)
   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(2)])
    apply (rule image_subsetI)
    apply (rule iffD2)
     apply (rule proj_in_iff)
     apply (rule equiv_lsbis1[OF coalg_T])
    apply (erule rev_subsetD)
    apply (erule coalg_F1set2[OF coalg_T])
   apply (rule ord_eq_le_trans[OF F1.set_map(3)])
   apply (rule image_subsetI)
   apply (rule iffD2)
    apply (rule proj_in_iff)
    apply (rule equiv_lsbis2[OF coalg_T])
   apply (erule rev_subsetD)
   apply (erule coalg_F1set3[OF coalg_T])

  apply (rule univ_preserves)
    apply (rule equiv_lsbis2)
    apply (rule coalg_T)
   apply (rule congruent_strQ2)
  apply (rule ballI)
  apply (tactic \<open>stac @{context} @{thm o_apply} 1\<close>)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(2)])
   apply (rule image_subsetI)
   apply (rule iffD2)
    apply (rule proj_in_iff)
    apply (rule equiv_lsbis1[OF coalg_T])
   apply (erule rev_subsetD)
   apply (erule coalg_F2set2[OF coalg_T])
  apply (rule ord_eq_le_trans[OF F2.set_map(3)])
  apply (rule image_subsetI)
  apply (rule iffD2)
   apply (rule proj_in_iff)
   apply (rule equiv_lsbis2[OF coalg_T])
  apply (erule rev_subsetD)
  apply (erule coalg_F2set3[OF coalg_T])
  done

lemma mor_T_final:
  "mor carT1 carT2 strT1 strT2 car_final1 car_final2 str_final1 str_final2
  (Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2))
  (Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2))"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule iffD2)
     apply (rule proj_in_iff)
     apply (rule equiv_lsbis1[OF coalg_T])
    apply assumption
   apply (rule ballI)
   apply (rule iffD2)
    apply (rule proj_in_iff)
    apply (rule equiv_lsbis2[OF coalg_T])
   apply assumption

  apply (rule conjI)
   apply (rule ballI)
   apply (rule sym)
   apply (rule trans)
    apply (rule univ_commute)
      apply (rule equiv_lsbis1[OF coalg_T])
     apply (rule congruent_strQ1)
    apply assumption
   apply (rule o_apply)

  apply (rule ballI)
  apply (rule sym)
  apply (rule trans)
   apply (rule univ_commute)
     apply (rule equiv_lsbis2[OF coalg_T])
    apply (rule congruent_strQ2)
   apply assumption
  apply (rule o_apply)
  done

lemmas mor_final = mor_comp[OF mor_beh mor_T_final]
lemmas in_car_final1 = mor_image1'[OF mor_final UNIV_I]
lemmas in_car_final2 = mor_image2'[OF mor_final UNIV_I]


(* The final coalgebra as a type *)

typedef (overloaded) 'a JF1 = "car_final1 :: 'a carrier set set"
  by (rule exI) (rule in_car_final1)

typedef (overloaded) 'a JF2 = "car_final2 :: 'a carrier set set"
  by (rule exI) (rule in_car_final2)

(* unfold & unfold *)
definition dtor1 where
  "dtor1 x = F1map id Abs_JF1 Abs_JF2 (str_final1 (Rep_JF1 x))"
definition dtor2 where
  "dtor2 x = F2map id Abs_JF1 Abs_JF2 (str_final2 (Rep_JF2 x))"

lemma mor_Rep_JF: "mor UNIV UNIV dtor1 dtor2
  car_final1 car_final2 str_final1 str_final2
  Rep_JF1 Rep_JF2"
  unfolding mor_def dtor1_def dtor2_def
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule Rep_JF1)
   apply (rule ballI)
   apply (rule Rep_JF2)

  apply (rule conjI)
   apply (rule ballI)
   apply (rule trans[OF F1map_comp_id])
   apply (rule F1map_congL)
    apply (rule ballI)
    apply (rule trans[OF o_apply])
    apply (rule Abs_JF1_inverse)
    apply (erule rev_subsetD)
    apply (rule coalg_F1set2)
     apply (rule coalg_final)
    apply (rule Rep_JF1)
   apply (rule ballI)
   apply (rule trans[OF o_apply])
   apply (rule Abs_JF2_inverse)
   apply (erule rev_subsetD)
   apply (rule coalg_F1set3)
    apply (rule coalg_final)
   apply (rule Rep_JF1)

  apply (rule ballI)
  apply (rule trans[OF F2map_comp_id])
  apply (rule F2map_congL)
   apply (rule ballI)
   apply (rule trans[OF o_apply])
   apply (rule Abs_JF1_inverse)
   apply (erule rev_subsetD)
   apply (rule coalg_F2set2)
    apply (rule coalg_final)
   apply (rule Rep_JF2)
  apply (rule ballI)
  apply (rule trans[OF o_apply])
  apply (rule Abs_JF2_inverse)
  apply (erule rev_subsetD)
  apply (rule coalg_F2set3)
   apply (rule coalg_final)
  apply (rule Rep_JF2)
  done

lemma mor_Abs_JF: "mor car_final1 car_final2 str_final1 str_final2
  UNIV UNIV dtor1 dtor2 Abs_JF1 Abs_JF2"
  unfolding mor_def dtor1_def dtor2_def
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
   apply (rule UNIV_I)

  apply (rule conjI)
   apply (rule ballI)
   apply (erule sym[OF arg_cong[OF Abs_JF1_inverse]])
  apply (rule ballI)
  apply (erule sym[OF arg_cong[OF Abs_JF2_inverse]])
  done

definition unfold1 where
  "unfold1 s1 s2 x =
     Abs_JF1 ((Equiv_Relations.proj (lsbis1 carT1 carT2 strT1 strT2) o beh1 s1 s2) x)"
definition unfold2 where
  "unfold2 s1 s2 x =
     Abs_JF2 ((Equiv_Relations.proj (lsbis2 carT1 carT2 strT1 strT2) o beh2 s1 s2) x)"

lemma mor_unfold:
  "mor UNIV UNIV s1 s2 UNIV UNIV dtor1 dtor2 (unfold1 s1 s2) (unfold2 s1 s2)"
  apply (rule iffD2)
   apply (rule mor_UNIV)
  apply (rule conjI)
   apply (rule ext)
   apply (rule sym[OF trans[OF o_apply]])
   apply (rule trans[OF dtor1_def])
   apply (rule trans[OF arg_cong[OF unfold1_def]])
   apply (rule trans[OF arg_cong[OF Abs_JF1_inverse[OF in_car_final1]]])
   apply (rule trans[OF arg_cong[OF sym[OF morE1[OF mor_final UNIV_I]]]])
   apply (rule trans[OF F1map_comp_id])
   apply (rule sym[OF trans[OF o_apply]])
   apply (rule F1.map_cong0)
     apply (rule refl)
    apply (rule trans[OF unfold1_def])
    apply (rule sym[OF o_apply])
   apply (rule trans[OF unfold2_def])
   apply (rule sym[OF o_apply])

  apply (rule ext)
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule trans[OF dtor2_def])
  apply (rule trans[OF arg_cong[OF unfold2_def]])
  apply (rule trans[OF arg_cong[OF Abs_JF2_inverse[OF in_car_final2]]])
  apply (rule trans[OF arg_cong[OF sym[OF morE2[OF mor_final UNIV_I]]]])
  apply (rule trans[OF F2map_comp_id])
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule F2.map_cong0)
    apply (rule refl)
   apply (rule trans[OF unfold1_def])
   apply (rule sym[OF o_apply])
  apply (rule trans[OF unfold2_def])
  apply (rule sym[OF o_apply])
  done

lemmas unfold1 = sym[OF morE1[OF mor_unfold UNIV_I]]
lemmas unfold2 = sym[OF morE2[OF mor_unfold UNIV_I]]

lemma JF_cind: "sbis UNIV UNIV dtor1 dtor2 R1 R2 \<Longrightarrow> R1 \<subseteq> Id \<and> R2 \<subseteq> Id"
  apply (rule rev_mp)
   apply (tactic \<open>forward_tac @{context} @{thms bis_def[THEN iffD1]} 1\<close>)
   apply (erule conjE)+
   apply (rule bis_cong)
     apply (rule bis_Comp)
      apply (rule bis_converse)
      apply (rule bis_Gr)
       apply (rule tcoalg)
      apply (rule mor_Rep_JF)
     apply (rule bis_Comp)
      apply assumption
     apply (rule bis_Gr)
      apply (rule tcoalg)
     apply (rule mor_Rep_JF)
    apply (erule relImage_Gr)
   apply (erule relImage_Gr)

  apply (rule impI)
  apply (rule rev_mp)
   apply (rule bis_cong)
     apply (rule bis_Comp)
      apply (rule bis_Gr)
       apply (rule coalg_T)
      apply (rule mor_T_final)
     apply (rule bis_Comp)
      apply (rule sbis_lsbis)
     apply (rule bis_converse)
     apply (rule bis_Gr)
      apply (rule coalg_T)
     apply (rule mor_T_final)
    apply (rule relInvImage_Gr[OF lsbis1_incl])
   apply (rule relInvImage_Gr[OF lsbis2_incl])

  apply (rule impI)
  apply (rule conjI)
   apply (rule subset_trans)
    apply (rule relInvImage_UNIV_relImage)
   apply (rule subset_trans)
    apply (rule relInvImage_mono)
    apply (rule subset_trans)
     apply (erule incl_lsbis1)
    apply (rule ord_eq_le_trans)
     apply (rule sym[OF relImage_relInvImage])
     apply (rule xt1(3))
      apply (rule Sigma_cong)
       apply (rule proj_image)
      apply (rule proj_image)
     apply (rule lsbis1_incl)
    apply (rule subset_trans)
     apply (rule relImage_mono)
     apply (rule incl_lsbis1)
     apply assumption
    apply (rule relImage_proj)
    apply (rule equiv_lsbis1[OF coalg_T])
   apply (rule relInvImage_Id_on)
   apply (rule Rep_JF1_inject)

  apply (rule subset_trans)
   apply (rule relInvImage_UNIV_relImage)
  apply (rule subset_trans)
   apply (rule relInvImage_mono)
   apply (rule subset_trans)
    apply (erule incl_lsbis2)
   apply (rule ord_eq_le_trans)
    apply (rule sym[OF relImage_relInvImage])
    apply (rule xt1(3))
     apply (rule Sigma_cong)
      apply (rule proj_image)
     apply (rule proj_image)
    apply (rule lsbis2_incl)
   apply (rule subset_trans)
    apply (rule relImage_mono)
    apply (rule incl_lsbis2)
    apply assumption
   apply (rule relImage_proj)
   apply (rule equiv_lsbis2[OF coalg_T])
  apply (rule relInvImage_Id_on)
  apply (rule Rep_JF2_inject)
  done

lemmas JF_cind1 = conjunct1[OF JF_cind]
lemmas JF_cind2 = conjunct2[OF JF_cind]

lemma unfold_unique_mor:
  "mor UNIV UNIV s1 s2 UNIV UNIV dtor1 dtor2 f1 f2 \<Longrightarrow>
   f1 = unfold1 s1 s2 \<and> f2 = unfold2 s1 s2"
  apply (rule conjI)
   apply (rule ext)
   apply (erule IdD[OF subsetD[OF JF_cind1[OF bis_image2[OF tcoalg _ tcoalg]]]])
    apply (rule mor_comp[OF mor_final mor_Abs_JF])
   apply (rule image2_eqI)
     apply (rule refl)
    apply (rule trans[OF arg_cong[OF unfold1_def]])
    apply (rule sym[OF o_apply])
   apply (rule UNIV_I)

  apply (rule ext)
  apply (erule IdD[OF subsetD[OF JF_cind2[OF bis_image2[OF tcoalg _ tcoalg]]]])
   apply (rule mor_comp[OF mor_final mor_Abs_JF])
  apply (rule image2_eqI)
    apply (rule refl)
   apply (rule trans[OF arg_cong[OF unfold2_def]])
   apply (rule sym[OF o_apply])
  apply (rule UNIV_I)
  done

lemmas unfold_unique = unfold_unique_mor[OF iffD2[OF mor_UNIV], OF conjI]
lemmas unfold1_dtor = sym[OF conjunct1[OF unfold_unique_mor[OF mor_id]]]
lemmas unfold2_dtor = sym[OF conjunct2[OF unfold_unique_mor[OF mor_id]]]

lemmas unfold1_o_dtor1 =
  trans[OF conjunct1[OF unfold_unique_mor[OF mor_comp[OF mor_str mor_unfold]]] unfold1_dtor]
lemmas unfold2_o_dtor2 =
  trans[OF conjunct2[OF unfold_unique_mor[OF mor_comp[OF mor_str mor_unfold]]] unfold2_dtor]

(* the fold operator *)
definition ctor1 where "ctor1 = unfold1 (F1map id dtor1 dtor2) (F2map id dtor1 dtor2)"
definition ctor2 where "ctor2 = unfold2 (F1map id dtor1 dtor2) (F2map id dtor1 dtor2)"

lemma ctor1_o_dtor1:
  "ctor1 o dtor1 = id"
  unfolding ctor1_def
  apply (rule unfold1_o_dtor1)
  done

lemma ctor2_o_dtor2:
  "ctor2 o dtor2 = id"
  unfolding ctor2_def
  apply (rule unfold2_o_dtor2)
  done

lemma dtor1_o_ctor1:
  "dtor1 o ctor1 = id"
  unfolding ctor1_def
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF unfold1])
  apply (rule trans[OF F1map_comp_id])
  apply (rule trans[OF F1map_congL])
    apply (rule ballI)
    apply (rule trans[OF fun_cong[OF unfold1_o_dtor1] id_apply])
   apply (rule ballI)
   apply (rule trans[OF fun_cong[OF unfold2_o_dtor2] id_apply])
  apply (rule sym[OF id_apply])
  done

lemma dtor2_o_ctor2:
  "dtor2 o ctor2 = id"
  unfolding ctor2_def
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF unfold2])
  apply (rule trans[OF F2map_comp_id])
  apply (rule trans[OF F2map_congL])
    apply (rule ballI)
    apply (rule trans[OF fun_cong[OF unfold1_o_dtor1] id_apply])
   apply (rule ballI)
   apply (rule trans[OF fun_cong[OF unfold2_o_dtor2] id_apply])
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

lemmas ctor1_unfold1 = iffD1[OF dtor1_diff trans[OF unfold1 sym[OF dtor1_ctor1]]]
lemmas ctor2_unfold2 = iffD1[OF dtor2_diff trans[OF unfold2 sym[OF dtor2_ctor2]]]

(* corecursor: *)

definition corec1 where "corec1 s1 s2 =
  unfold1 (case_sum (F1map id Inl Inl o dtor1) s1)
          (case_sum (F2map id Inl Inl o dtor2) s2) o Inr"
definition corec2 where "corec2 s1 s2 =
  unfold2 (case_sum (F1map id Inl Inl o dtor1) s1)
          (case_sum (F2map id Inl Inl o dtor2) s2) o Inr"

lemma dtor1_o_unfold1: "dtor1 o unfold1 s1 s2 = F1map id (unfold1 s1 s2) (unfold2 s1 s2) o s1"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm unfold1}) 1\<close>)
lemma dtor2_o_unfold2: "dtor2 o unfold2 s1 s2 = F2map id (unfold1 s1 s2) (unfold2 s1 s2) o s2"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm unfold2}) 1\<close>)

lemma corec1_Inl_sum:
  "unfold1 (case_sum (F1map id Inl Inl \<circ> dtor1) s1) (case_sum (F2map id Inl Inl \<circ> dtor2) s2) \<circ> Inl = id"
  apply (rule trans[OF conjunct1[OF unfold_unique] unfold1_dtor])
   apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF F1.map_comp0[of id, unfolded id_o] refl]])
   apply (rule sym[OF trans[OF o_assoc]])
   apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF dtor1_o_unfold1 refl]])
   apply (rule box_equals[OF _ o_assoc o_assoc])
   apply (rule arg_cong2[of _ _ _ _ "(o)", OF refl case_sum_o_inj(1)])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF F2.map_comp0[of id, unfolded id_o] refl]])
  apply (rule sym[OF trans[OF o_assoc]])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF dtor2_o_unfold2 refl]])
  apply (rule box_equals[OF _ o_assoc o_assoc])
  apply (rule arg_cong2[of _ _ _ _ "(o)", OF refl case_sum_o_inj(1)])
  done

lemma corec2_Inl_sum:
  "unfold2 (case_sum (F1map id Inl Inl \<circ> dtor1) s1) (case_sum (F2map id Inl Inl \<circ> dtor2) s2) \<circ> Inl = id"
  apply (rule trans[OF conjunct2[OF unfold_unique] unfold2_dtor])
   apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF F1.map_comp0[of id, unfolded id_o] refl]])
   apply (rule sym[OF trans[OF o_assoc]])
   apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF dtor1_o_unfold1 refl]])
   apply (rule box_equals[OF _ o_assoc o_assoc])
   apply (rule arg_cong2[of _ _ _ _ "(o)", OF refl case_sum_o_inj(1)])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF F2.map_comp0[of id, unfolded id_o] refl]])
  apply (rule sym[OF trans[OF o_assoc]])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF dtor2_o_unfold2 refl]])
  apply (rule box_equals[OF _ o_assoc o_assoc])
  apply (rule arg_cong2[of _ _ _ _ "(o)", OF refl case_sum_o_inj(1)])
  done

lemma case_sum_expand_Inr: "f o Inl = g \<Longrightarrow> case_sum g (f o Inr) = f"
  by (auto split: sum.splits)

theorem corec1:
  "dtor1 (corec1 s1 s2 a) =
    F1map id (case_sum id (corec1 s1 s2)) (case_sum id (corec2 s1 s2)) (s1 a)"
  unfolding corec1_def corec2_def o_apply unfold1 sum.case
    case_sum_expand_Inr[OF corec1_Inl_sum] case_sum_expand_Inr[OF corec2_Inl_sum] ..

theorem corec2:
  "dtor2 (corec2 s1 s2 a) =
    F2map id (case_sum id (corec1 s1 s2)) (case_sum id (corec2 s1 s2)) (s2 a)"
  unfolding corec1_def corec2_def o_apply unfold2 sum.case
    case_sum_expand_Inr[OF corec1_Inl_sum] case_sum_expand_Inr[OF corec2_Inl_sum] ..

lemma corec_unique:
  "F1map id (case_sum id f1) (case_sum id f2) \<circ> s1 = dtor1 \<circ> f1 \<Longrightarrow>
   F2map id (case_sum id f1) (case_sum id f2) \<circ> s2 = dtor2 \<circ> f2 \<Longrightarrow>
   f1 = corec1 s1 s2 \<and> f2 = corec2 s1 s2"
  unfolding corec1_def corec2_def case_sum_expand_Inr'[OF corec1_Inl_sum] case_sum_expand_Inr'[OF corec2_Inl_sum]
  apply (rule unfold_unique)
   apply (unfold o_case_sum id_o o_id F1.map_comp0[symmetric] F2.map_comp0[symmetric]
      F1.map_id0 F2.map_id0 o_assoc case_sum_o_inj(1))
   apply (erule arg_cong2[of _ _ _ _ case_sum, OF refl])
  apply (erule arg_cong2[of _ _ _ _ case_sum, OF refl])
  done

subsection \<open>Coinduction\<close>

lemma Frel_coind:
  "\<lbrakk>\<forall>a b. phi1 a b \<longrightarrow> F1rel (=) phi1 phi2 (dtor1 a) (dtor1 b);
    \<forall>a b. phi2 a b \<longrightarrow> F2rel (=) phi1 phi2 (dtor2 a) (dtor2 b)\<rbrakk> \<Longrightarrow>
   (phi1 a1 b1 \<longrightarrow> a1 = b1) \<and> (phi2 a2 b2 \<longrightarrow> a2 = b2)"
  apply (rule rev_mp)
   apply (rule JF_cind)
   apply (rule iffD2)
    apply (rule bis_Frel)
   apply (rule conjI)

    apply (rule conjI)
     apply (rule ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]])
    apply (rule ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]])

   apply (rule conjI)
    apply (rule allI)+
    apply (rule impI)
    apply (erule allE)+
    apply (rule predicate2D[OF eq_refl[OF F1rel_cong]])
       apply (rule refl)
      apply (rule in_rel_Collect_case_prod_eq[symmetric])
     apply (rule in_rel_Collect_case_prod_eq[symmetric])
    apply (erule mp)
    apply (erule CollectE)
    apply (erule case_prodD)

   apply (rule allI)+
   apply (rule impI)
   apply (erule allE)+
   apply (rule predicate2D[OF eq_refl[OF F2rel_cong]])
      apply (rule refl)
     apply (rule in_rel_Collect_case_prod_eq[symmetric])
    apply (rule in_rel_Collect_case_prod_eq[symmetric])
   apply (erule mp)
   apply (erule CollectE)
   apply (erule case_prodD)


  apply (rule impI)
  apply (erule conjE)+

  apply (rule conjI)
   apply (rule impI)
   apply (rule IdD)
   apply (erule subsetD)
   apply (rule CollectI)
   apply (erule case_prodI)

  apply (rule impI)
  apply (rule IdD)
  apply (erule subsetD)
  apply (rule CollectI)
  apply (erule case_prodI)
  done

subsection \<open>The Result as an BNF\<close>

abbreviation JF1map where
  "JF1map u \<equiv> unfold1 (F1map u id id o dtor1) (F2map u id id o dtor2)"
abbreviation JF2map where
  "JF2map u \<equiv> unfold2 (F1map u id id o dtor1) (F2map u id id o dtor2)"

lemma JF1map: "dtor1 o JF1map u = F1map u (JF1map u) (JF2map u) o dtor1"
  apply (rule ext)
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule trans[OF unfold1])
  apply (rule box_equals[OF F1.map_comp _ F1.map_cong0, rotated])
     apply (rule fun_cong[OF id_o])
    apply (rule fun_cong[OF o_id])
   apply (rule fun_cong[OF o_id])
  apply (rule sym[OF arg_cong[OF o_apply]])
  done

lemma JF2map: "dtor2 o JF2map u = F2map u (JF1map u) (JF2map u) o dtor2"
  apply (rule ext)
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule trans[OF unfold2])
  apply (rule box_equals[OF F2.map_comp _ F2.map_cong0, rotated])
     apply (rule fun_cong[OF id_o])
    apply (rule fun_cong[OF o_id])
   apply (rule fun_cong[OF o_id])
  apply (rule sym[OF arg_cong[OF o_apply]])
  done

lemmas JF1map_simps = o_eq_dest[OF JF1map]
lemmas JF2map_simps = o_eq_dest[OF JF2map]

theorem JF1map_id: "JF1map id = id"
  apply (rule trans)
   apply (rule conjunct1)
   apply (rule unfold_unique)
    apply (rule sym[OF JF1map])
   apply (rule sym[OF JF2map])
  apply (rule unfold1_dtor)
  done

theorem JF2map_id: "JF2map id = id"
  apply (rule trans)
   apply (rule conjunct2)
   apply (rule unfold_unique)
    apply (rule sym[OF JF1map])
   apply (rule sym[OF JF2map])
  apply (rule unfold2_dtor)
  done

lemma JFmap_unique:
  "\<lbrakk>dtor1 o u = F1map f u v o dtor1; dtor2 o v = F2map f u v o dtor2\<rbrakk> \<Longrightarrow>
    u = JF1map f \<and> v = JF2map f"
  apply (rule unfold_unique)
  unfolding o_assoc F1.map_comp0[symmetric] F2.map_comp0[symmetric] id_o o_id
   apply (erule sym)
  apply (erule sym)
  done

theorem JF1map_comp: "JF1map (g o f) = JF1map g o JF1map f"
  apply (rule sym)
  apply (rule conjunct1)
  apply (rule JFmap_unique)
   apply (rule trans[OF o_assoc])
   apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF JF1map refl]])
   apply (rule trans[OF sym[OF o_assoc]])
   apply (rule trans[OF arg_cong[OF JF1map]])
   apply (rule trans[OF o_assoc])
   apply (rule arg_cong2[of _ _ _ _ "(o)", OF sym[OF F1.map_comp0] refl])

  apply (rule trans[OF o_assoc])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF JF2map refl]])
  apply (rule trans[OF sym[OF o_assoc]])
  apply (rule trans[OF arg_cong[OF JF2map]])
  apply (rule trans[OF o_assoc])
  apply (rule arg_cong2[of _ _ _ _ "(o)", OF sym[OF F2.map_comp0] refl])
  done

theorem JF2map_comp: "JF2map (g o f) = JF2map g o JF2map f"
  apply (rule sym)
  apply (rule conjunct2)
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm unfold_unique}) 1\<close>)

   apply (rule trans[OF o_assoc])
   apply (rule trans[OF arg_cong[OF sym[OF F2.map_comp0]]])
   apply (rule sym[OF trans[OF o_assoc]])
   apply (rule trans[OF arg_cong2[OF JF2map refl]])
   apply (rule trans[OF sym[OF o_assoc]])
   apply (rule trans[OF arg_cong[OF JF2map]])
   apply (rule trans[OF o_assoc])
   apply (rule trans[OF arg_cong2[OF sym[OF F2.map_comp0] refl]])
   apply (rule ext)
   apply (rule trans[OF o_apply])
   apply (rule sym)
   apply (rule trans[OF o_apply])
   apply (rule F2.map_cong0)
     apply (rule trans[OF o_apply])
     apply (rule id_apply)
    apply (rule trans[OF o_apply])
    apply (rule arg_cong[OF id_apply])
   apply (rule trans[OF o_apply])
   apply (rule arg_cong[OF id_apply])

  apply (rule trans[OF o_assoc])
  apply (rule trans[OF arg_cong[OF sym[OF F1.map_comp0]]])
  apply (rule sym[OF trans[OF o_assoc]])
  apply (rule trans[OF arg_cong2[OF JF1map refl]])
  apply (rule trans[OF sym[OF o_assoc]])
  apply (rule trans[OF arg_cong[OF JF1map]])
  apply (rule trans[OF o_assoc])
  apply (rule trans[OF arg_cong2[OF sym[OF F1.map_comp0] refl]])
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (rule F1.map_cong0)
    apply (rule trans[OF o_apply])
    apply (rule id_apply)
   apply (rule trans[OF o_apply])
   apply (rule arg_cong[OF id_apply])
  apply (rule trans[OF o_apply])
  apply (rule arg_cong[OF id_apply])
  done

(* The hereditary F-sets1: *)
definition JFcol where
  "JFcol = rec_nat (%a. {}, %b. {})
     (%n rec.
     (%a. F1set1 (dtor1 a) \<union>
       ((\<Union>a' \<in> F1set2 (dtor1 a). fst rec a') \<union>
       (\<Union>a' \<in> F1set3 (dtor1 a). snd rec a')),
      %b. F2set1 (dtor2 b) \<union>
       ((\<Union>b' \<in> F2set2 (dtor2 b). fst rec b') \<union>
       (\<Union>b' \<in> F2set3 (dtor2 b). snd rec b'))))"

abbreviation JF1col where "JF1col n \<equiv> fst (JFcol n)"
abbreviation JF2col where "JF2col n \<equiv> snd (JFcol n)"

lemmas JF1col_0 = fun_cong[OF fstI[OF rec_nat_0_imp[OF JFcol_def]]]
lemmas JF2col_0 = fun_cong[OF sndI[OF rec_nat_0_imp[OF JFcol_def]]]
lemmas JF1col_Suc = fun_cong[OF fstI[OF rec_nat_Suc_imp[OF JFcol_def]]]
lemmas JF2col_Suc = fun_cong[OF sndI[OF rec_nat_Suc_imp[OF JFcol_def]]]

lemma JFcol_minimal:
  "\<lbrakk>\<And>a. F1set1 (dtor1 a) \<subseteq> K1 a;
    \<And>b. F2set1 (dtor2 b) \<subseteq> K2 b;
    \<And>a a'. a' \<in> F1set2 (dtor1 a) \<Longrightarrow> K1 a' \<subseteq> K1 a;
    \<And>a b'. b' \<in> F1set3 (dtor1 a) \<Longrightarrow> K2 b' \<subseteq> K1 a;
    \<And>b a'. a' \<in> F2set2 (dtor2 b) \<Longrightarrow> K1 a' \<subseteq> K2 b;
    \<And>b b'. b' \<in> F2set3 (dtor2 b) \<Longrightarrow> K2 b' \<subseteq> K2 b\<rbrakk> \<Longrightarrow>
  \<forall>a b. JF1col n a \<subseteq> K1 a \<and> JF2col n b \<subseteq> K2 b"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule JF1col_0)
    apply (rule empty_subsetI)

   apply (rule ord_eq_le_trans)
    apply (rule JF2col_0)
   apply (rule empty_subsetI)

  apply (rule allI)+
  apply (rule conjI)
   apply (rule ord_eq_le_trans)
    apply (rule JF1col_Suc)
   apply (rule Un_least)
    apply assumption
   apply (rule Un_least)
    apply (rule UN_least)
    apply (erule allE conjE)+
    apply (rule subset_trans)
     apply assumption
    apply assumption

   apply (rule UN_least)
   apply (erule allE conjE)+
   apply (rule subset_trans)
    apply assumption
   apply assumption

(**)

  apply (rule ord_eq_le_trans)
   apply (rule JF2col_Suc)
  apply (rule Un_least)
   apply assumption
  apply (rule Un_least)
   apply (rule UN_least)
   apply (erule allE conjE)+
   apply (rule subset_trans)
    apply assumption
   apply assumption

  apply (rule UN_least)
  apply (erule allE conjE)+
  apply (rule subset_trans)
   apply assumption
  apply assumption
  done

lemma JFset_minimal:
  "\<lbrakk>\<And>a. F1set1 (dtor1 a) \<subseteq> K1 a;
    \<And>b. F2set1 (dtor2 b) \<subseteq> K2 b;
    \<And>a a'. a' \<in> F1set2 (dtor1 a) \<Longrightarrow> K1 a' \<subseteq> K1 a;
    \<And>a b'. b' \<in> F1set3 (dtor1 a) \<Longrightarrow> K2 b' \<subseteq> K1 a;
    \<And>b a'. a' \<in> F2set2 (dtor2 b) \<Longrightarrow> K1 a' \<subseteq> K2 b;
    \<And>b b'. b' \<in> F2set3 (dtor2 b) \<Longrightarrow> K2 b' \<subseteq> K2 b\<rbrakk> \<Longrightarrow>
  (\<Union>n. JF1col n a) \<subseteq> K1 a \<and> (\<Union>n. JF2col n b) \<subseteq> K2 b"
  apply (rule conjI)
   apply (rule UN_least)
   apply (rule rev_mp)
    apply (rule JFcol_minimal)
         apply assumption
        apply assumption
       apply assumption
      apply assumption
     apply assumption
    apply assumption
   apply (rule impI)
   apply (erule allE conjE)+
   apply assumption

  apply (rule UN_least)
  apply (rule rev_mp)
   apply (rule JFcol_minimal)
        apply assumption
       apply assumption
      apply assumption
     apply assumption
    apply assumption
   apply assumption
  apply (rule impI)
  apply (erule allE conjE)+
  apply assumption
  done

abbreviation JF1set where "JF1set a \<equiv> (\<Union>n. JF1col n a)"
abbreviation JF2set where "JF2set a \<equiv> (\<Union>n. JF2col n a)"

lemma F1set1_incl_JF1set:
  "F1set1 (dtor1 a) \<subseteq> JF1set a"
  apply (rule SUP_upper2)
   apply (rule UNIV_I)
  apply (rule ord_le_eq_trans)
   apply (rule Un_upper1)
  apply (rule sym)
  apply (rule JF1col_Suc)
  done

lemma F2set1_incl_JF2set:
  "F2set1 (dtor2 a) \<subseteq> JF2set a"
  apply (rule SUP_upper2)
   apply (rule UNIV_I)
  apply (rule ord_le_eq_trans)
   apply (rule Un_upper1)
  apply (rule sym)
  apply (rule JF2col_Suc)
  done

lemma F1set2_JF1set_incl_JF1set:
  "a' \<in> F1set2 (dtor1 a) \<Longrightarrow> JF1set a' \<subseteq> JF1set a"
  apply (rule UN_least)
  apply (rule subsetI)
  apply (rule UN_I)
   apply (rule UNIV_I)
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule JF1col_Suc)
  apply (rule UnI2)
  apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN 2 1) 1\<close>)
  apply (erule UN_I)
  apply assumption
  done

lemma F1set3_JF2set_incl_JF1set:
  "a' \<in> F1set3 (dtor1 a) \<Longrightarrow> JF2set a' \<subseteq> JF1set a"
  apply (rule UN_least)
  apply (rule subsetI)
  apply (rule UN_I)
   apply (rule UNIV_I)
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule JF1col_Suc)
  apply (rule UnI2)
  apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN  2 2) 1\<close>)
  apply (erule UN_I)
  apply assumption
  done

lemma F2set2_JF1set_incl_JF2set:
  "a' \<in> F2set2 (dtor2 a) \<Longrightarrow> JF1set a' \<subseteq> JF2set a"
  apply (rule UN_least)
  apply (rule subsetI)
  apply (rule UN_I)
   apply (rule UNIV_I)
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule JF2col_Suc)
  apply (rule UnI2)
  apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN  2 1) 1\<close>)
  apply (erule UN_I)
  apply assumption
  done

lemma F2set3_JF2set_incl_JF2set:
  "a' \<in> F2set3 (dtor2 a) \<Longrightarrow> JF2set a' \<subseteq> JF2set a"
  apply (rule UN_least)
  apply (rule subsetI)
  apply (rule UN_I)
   apply (rule UNIV_I)
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule JF2col_Suc)
  apply (rule UnI2)
  apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN  2 2) 1\<close>)
  apply (erule UN_I)
  apply assumption
  done

lemmas F1set1_JF1set = subsetD[OF F1set1_incl_JF1set]
lemmas F2set1_JF2set = subsetD[OF F2set1_incl_JF2set]
lemmas F1set2_JF1set_JF1set = subsetD[OF F1set2_JF1set_incl_JF1set]
lemmas F1set3_JF2set_JF1set = subsetD[OF F1set3_JF2set_incl_JF1set]
lemmas F2set2_JF1set_JF2set = subsetD[OF F2set2_JF1set_incl_JF2set]
lemmas F2set3_JF2set_JF2set = subsetD[OF F2set3_JF2set_incl_JF2set]

lemma JFset_le:
  fixes a :: "'a JF1" and b :: "'a JF2"
  shows
    "JF1set a \<subseteq> F1set1 (dtor1 a) \<union> (\<Union> (JF1set ` F1set2 (dtor1 a)) \<union> \<Union> (JF2set ` F1set3 (dtor1 a))) \<and>
    JF2set b \<subseteq> F2set1 (dtor2 b) \<union> (\<Union> (JF1set ` F2set2 (dtor2 b)) \<union> \<Union> (JF2set ` F2set3 (dtor2 b)))"
  apply (rule JFset_minimal)
       apply (rule Un_upper1)
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN 2 1) 1\<close>)
     apply (erule UN_I)
     apply (erule UnE)
      apply (erule F1set1_JF1set)
     apply (erule UnE)+
      apply (erule UN_E)
      apply (erule F1set2_JF1set_JF1set)
      apply assumption
     apply (erule UN_E)
     apply (erule F1set3_JF2set_JF1set)
     apply assumption
    apply (rule subsetI)
    apply (rule UnI2)
    apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN 2 2) 1\<close>)
    apply (erule UN_I)
    apply (erule UnE)
     apply (erule F2set1_JF2set)
    apply (erule UnE)+
     apply (erule UN_E)
     apply (erule F2set2_JF1set_JF2set)
     apply assumption
    apply (erule UN_E)
    apply (erule F2set3_JF2set_JF2set)
    apply assumption
   apply (rule subsetI)
   apply (rule UnI2)
   apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN 2 1) 1\<close>)
   apply (erule UN_I)
   apply (erule UnE)+
    apply (erule F1set1_JF1set)
   apply (erule UnE)+
    apply (erule UN_E)
    apply (erule F1set2_JF1set_JF1set)
    apply assumption
   apply (erule UN_E)
   apply (erule F1set3_JF2set_JF1set)
   apply assumption
  apply (rule subsetI)
  apply (rule UnI2)
  apply (tactic \<open>rtac @{context} (BNF_Util.mk_UnIN 2 2) 1\<close>)
  apply (erule UN_I)
  apply (erule UnE)+
   apply (erule F2set1_JF2set)
  apply (erule UnE)+
   apply (erule UN_E)
   apply (erule F2set2_JF1set_JF2set)
   apply assumption
  apply (erule UN_E)
  apply (erule F2set3_JF2set_JF2set)
  apply assumption
  done

theorem JF1set_simps:
  "JF1set a = F1set1 (dtor1 a) \<union>
    ((\<Union> b \<in> F1set2 (dtor1 a). JF1set b) \<union>
     (\<Union> b \<in> F1set3 (dtor1 a). JF2set b))"
  apply (rule equalityI)
   apply (rule conjunct1[OF JFset_le])
  apply (rule Un_least)
   apply (rule F1set1_incl_JF1set)
  apply (rule Un_least)
   apply (rule UN_least)
   apply (erule F1set2_JF1set_incl_JF1set)
  apply (rule UN_least)
  apply (erule F1set3_JF2set_incl_JF1set)
  done

theorem JF2set_simps:
  "JF2set a = F2set1 (dtor2 a) \<union>
    ((\<Union> b \<in> F2set2 (dtor2 a). JF1set b) \<union>
     (\<Union> b \<in> F2set3 (dtor2 a). JF2set b))"
  apply (rule equalityI)
   apply (rule conjunct2[OF JFset_le])
  apply (rule Un_least)
   apply (rule F2set1_incl_JF2set)
  apply (rule Un_least)
   apply (rule UN_least)
   apply (erule F2set2_JF1set_incl_JF2set)
  apply (rule UN_least)
  apply (erule F2set3_JF2set_incl_JF2set)
  done

lemma JFcol_natural:
  "\<forall>b1 b2. u ` (JF1col n b1) = JF1col n (JF1map u b1) \<and>
           u ` (JF2col n b2) = JF2col n (JF2map u b2)"
  apply (rule nat_induct)
   apply (rule allI)+
  unfolding JF1col_0 JF2col_0
   apply (rule conjI)
    apply (rule image_empty)
   apply (rule image_empty)

  apply (rule allI)+
  apply (rule conjI)
   apply (unfold JF1col_Suc JF1map_simps image_Un image_UN UN_simps(10)
      F1.set_map(1) F1.set_map(2) F1.set_map(3)) [1]
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule refl)
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule SUP_cong[OF refl])
    apply (erule allE)+
    apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule SUP_cong[OF refl])
   apply (erule allE)+
   apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)

  apply (unfold JF2col_Suc JF2map_simps image_Un image_UN UN_simps(10)
      F2.set_map(1) F2.set_map(2) F2.set_map(3)) [1]
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule refl)
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule SUP_cong[OF refl])
   apply (erule allE)+
   apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
  apply (rule SUP_cong[OF refl])
  apply (erule allE)+
  apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  done

theorem JF1set_natural: "JF1set o (JF1map u) = image u o JF1set"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF image_UN])
  apply (rule SUP_cong[OF refl])
  apply (rule conjunct1)
  apply (rule spec[OF spec[OF JFcol_natural]])
  done

theorem JF2set_natural: "JF2set o (JF2map u) = image u o JF2set"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF image_UN])
  apply (rule SUP_cong[OF refl])
  apply (rule conjunct2)
  apply (rule spec[OF spec[OF JFcol_natural]])
  done

theorem JFmap_cong0:
  "((\<forall>p \<in> JF1set a. u p = v p) \<longrightarrow> JF1map u a = JF1map v a) \<and>
   ((\<forall>p \<in> JF2set b. u p = v p) \<longrightarrow> JF2map u b = JF2map v b)"
  apply (rule rev_mp)
   apply (rule Frel_coind[of
        "%b c. \<exists>a. a \<in> {a. \<forall>p \<in> JF1set a. u p = v p} \<and> b = JF1map u a \<and> c = JF1map v a"
        "%b c. \<exists>a. a \<in> {a. \<forall>p \<in> JF2set a. u p = v p} \<and> b = JF2map u a \<and> c = JF2map v a"])
    apply (intro allI impI iffD2[OF F1.in_rel])

    apply (erule exE conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule exI)

    apply (rule conjI[rotated])
     apply (rule conjI)
      apply (rule trans[OF F1.map_comp])
      apply (rule sym)
      apply (rule trans[OF JF1map_simps])
      apply (rule F1.map_cong0)
        apply (rule sym[OF trans[OF o_apply]])
        apply (rule fst_conv)
       apply (rule sym[OF fun_cong[OF fst_convol[unfolded convol_def]]])
      apply (rule sym[OF fun_cong[OF fst_convol[unfolded convol_def]]])

     apply (rule trans[OF F1.map_comp])
     apply (rule sym)
     apply (rule trans[OF JF1map_simps])
     apply (rule F1.map_cong0)
       apply (rule sym[OF trans[OF o_apply]])
       apply (rule trans[OF snd_conv])
       apply (erule CollectE)
       apply (erule bspec)
       apply (erule F1set1_JF1set)
      apply (rule sym[OF fun_cong[OF snd_convol[unfolded convol_def]]])
     apply (rule sym[OF fun_cong[OF snd_convol[unfolded convol_def]]])

    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(1))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule refl)

    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (rule ballI)
      apply (erule CollectE)
      apply (erule bspec)
      apply (erule F1set2_JF1set_JF1set)
      apply assumption
     apply (rule conjI[OF refl refl])

    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(3))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (rule ballI)
     apply (erule CollectE)
     apply (erule bspec)
     apply (erule F1set3_JF2set_JF1set)
     apply assumption
    apply (rule conjI[OF refl refl])


(**)

   apply (intro allI impI iffD2[OF F2.in_rel])

   apply (erule exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule exI)

   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans[OF F2.map_comp])
     apply (rule sym)
     apply (rule trans[OF JF2map_simps])
     apply (rule F2.map_cong0)
       apply (rule sym[OF trans[OF o_apply]])
       apply (rule fst_conv)
      apply (rule sym[OF fun_cong[OF fst_convol[unfolded convol_def]]])
     apply (rule sym[OF fun_cong[OF fst_convol[unfolded convol_def]]])

    apply (rule trans[OF F2.map_comp])
    apply (rule sym)
    apply (rule trans[OF JF2map_simps])
    apply (rule F2.map_cong0)
      apply (rule sym[OF trans[OF o_apply]])
      apply (rule trans[OF snd_conv])
      apply (erule CollectE)
      apply (erule bspec)
      apply (erule F2set1_JF2set)
     apply (rule sym[OF fun_cong[OF snd_convol[unfolded convol_def]]])
    apply (rule sym[OF fun_cong[OF snd_convol[unfolded convol_def]]])

   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(1))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule refl)

   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(2))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (rule ballI)
     apply (erule CollectE)
     apply (erule bspec)
     apply (erule F2set2_JF1set_JF2set)
     apply assumption
    apply (rule conjI[OF refl refl])

   apply (rule ord_eq_le_trans)
    apply (rule F2.set_map(3))
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule case_prodI)
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule ballI)
    apply (erule CollectE)
    apply (erule bspec)
    apply (erule F2set3_JF2set_JF2set)
    apply assumption
   apply (rule conjI[OF refl refl])

(**)

  apply (rule impI)

  apply (rule conjI)
   apply (rule impI)
   apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (erule mp)
   apply (rule exI)
   apply (rule conjI)
    apply (erule CollectI)
   apply (rule conjI)
    apply (rule refl)
   apply (rule refl)

  apply (rule impI)
  apply (tactic \<open>dtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
  apply (erule mp)
  apply (rule exI)
  apply (rule conjI)
   apply (erule CollectI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule refl)
  done

lemmas JF1map_cong0 = mp[OF conjunct1[OF JFmap_cong0]]
lemmas JF2map_cong0 = mp[OF conjunct2[OF JFmap_cong0]]

lemma JFcol_bd: "\<forall>(j1 :: 'a JF1) (j2 :: 'a JF2). |JF1col n j1| \<le>o bd_F \<and> |JF2col n j2| \<le>o bd_F"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule conjI)
    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_ordIso_subst)
     apply (rule JF1col_0)
    apply (rule Card_order_empty)
    apply (rule bd_F_Card_order)
   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule JF2col_0)
   apply (rule Card_order_empty)
   apply (rule bd_F_Card_order)

  apply (rule allI)+
  apply (rule conjI)
   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule JF1col_Suc)
   apply (rule Un_Cinfinite_bound)
     apply (rule F1set1_bd')
    apply (rule Un_Cinfinite_bound)
      apply (rule UNION_Cinfinite_bound)
        apply (rule F1set2_bd')
       apply (rule ballI)
       apply (erule allE)+
       apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
      apply (rule bd_F_Cinfinite)
     apply (rule UNION_Cinfinite_bound)
       apply (rule F1set3_bd')
      apply (rule ballI)
      apply (erule allE)+
      apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
     apply (rule bd_F_Cinfinite)
    apply (rule bd_F_Cinfinite)
   apply (rule bd_F_Cinfinite)

  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst)
   apply (rule JF2col_Suc)
  apply (rule Un_Cinfinite_bound)
    apply (rule F2set1_bd')
   apply (rule Un_Cinfinite_bound)
     apply (rule UNION_Cinfinite_bound)
       apply (rule F2set2_bd')
      apply (rule ballI)
      apply (erule allE)+
      apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
     apply (rule bd_F_Cinfinite)
    apply (rule UNION_Cinfinite_bound)
      apply (rule F2set3_bd')
     apply (rule ballI)
     apply (erule allE)+
     apply (tactic \<open>etac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
    apply (rule bd_F_Cinfinite)
   apply (rule bd_F_Cinfinite)
  apply (rule bd_F_Cinfinite)
  done

theorem JF1set_bd: "|JF1set j| \<le>o bd_F"
  apply (rule UNION_Cinfinite_bound)
    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_nat)
    apply (rule natLeq_ordLeq_cinfinite)
    apply (rule bd_F_Cinfinite)
   apply (rule ballI)
   apply (tactic \<open>rtac @{context} (BNF_Util.mk_conjunctN 2 1) 1\<close>)
   apply (rule spec[OF spec[OF JFcol_bd]])
  apply (rule bd_F_Cinfinite)
  done

theorem JF2set_bd: "|JF2set j| \<le>o bd_F"
  apply (rule UNION_Cinfinite_bound)
    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_nat)
    apply (rule natLeq_ordLeq_cinfinite)
    apply (rule bd_F_Cinfinite)
   apply (rule ballI)
   apply (tactic \<open>rtac @{context} (BNF_Util.mk_conjunctN 2 2) 1\<close>)
   apply (rule spec[OF spec[OF JFcol_bd]])
  apply (rule bd_F_Cinfinite)
  done

abbreviation "JF2wit \<equiv> ctor2 wit_F2"

theorem JF2wit: "\<And>x. x \<in> JF2set JF2wit \<Longrightarrow> False"
  apply (drule rev_subsetD)
   apply (rule equalityD1)
   apply (rule JF2set_simps)
  unfolding dtor2_ctor2
  apply (erule UnE)
   apply (erule F2.wit)
  apply (erule UnE)
   apply (erule UN_E)
   apply (erule F2.wit)
  apply (erule UN_E)
  apply (erule F2.wit)
  done

abbreviation "JF1wit \<equiv> (%a. ctor1 (wit2_F1 a JF2wit))"

theorem JF1wit: "\<And>x. x \<in> JF1set (JF1wit a) \<Longrightarrow> x = a"
  apply (drule rev_subsetD)
   apply (rule equalityD1)
   apply (rule JF1set_simps)
  unfolding dtor1_ctor1
  apply (erule UnE)+
   apply (erule F1.wit2)
  apply (erule UnE)
   apply (erule UN_E)
   apply (drule F1.wit2)
   apply (erule FalseE)
  apply (erule UN_E)
  apply (drule F1.wit2)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (drule rev_subsetD)
   apply (rule equalityD1)
   apply (rule JF2set_simps)
  unfolding dtor2_ctor2
  apply (erule UnE)+
   apply (drule F2.wit)
   apply (erule FalseE)
  apply (erule UnE)
   apply (erule UN_E)
   apply (drule F2.wit)
   apply (erule FalseE)
  apply (erule UN_E)
  apply (drule F2.wit)
  apply (erule FalseE)
  done

(* Additions: *)

context
  fixes phi1 :: "'a \<Rightarrow> 'a JF1 \<Rightarrow> bool" and phi2 :: "'a \<Rightarrow> 'a JF2 \<Rightarrow> bool"
begin

lemmas JFset_induct =
  JFset_minimal[of "%b1. {a \<in> JF1set b1 . phi1 a b1}" "%b2. {a \<in> JF2set b2 . phi2 a b2}",
    unfolded subset_Collect_iff[OF F1set1_incl_JF1set] subset_Collect_iff[OF F2set1_incl_JF2set]
    subset_Collect_iff[OF subset_refl],
    OF ballI ballI
    subset_CollectI[OF F1set2_JF1set_incl_JF1set]
    subset_CollectI[OF F1set3_JF2set_incl_JF1set]
    subset_CollectI[OF F2set2_JF1set_incl_JF2set]
    subset_CollectI[OF F2set3_JF2set_incl_JF2set]]

end

(*export that one!*)
ML \<open>rule_by_tactic @{context} (ALLGOALS (TRY o etac @{context} asm_rl)) @{thm JFset_induct}\<close>

(* Compositionality of relators *)

abbreviation JF1in where "JF1in B \<equiv> {a. JF1set a \<subseteq> B}"
abbreviation JF2in where "JF2in B \<equiv> {a. JF2set a \<subseteq> B}"

(* Notions and facts that make sense for any BNF: *)
definition JF1rel where
  "JF1rel R = (BNF_Def.Grp (JF1in (Collect (case_prod R))) (JF1map fst))^--1 OO
              (BNF_Def.Grp (JF1in (Collect (case_prod R))) (JF1map snd))"

definition JF2rel where
  "JF2rel R = (BNF_Def.Grp (JF2in (Collect (case_prod R))) (JF2map fst))^--1 OO
              (BNF_Def.Grp (JF2in (Collect (case_prod R))) (JF2map snd))"

lemma in_JF1rel:
  "JF1rel R x y \<longleftrightarrow> (\<exists> z. z \<in> JF1in (Collect (case_prod R)) \<and> JF1map fst z = x \<and> JF1map snd z = y)"
  by (rule predicate2_eqD[OF trans[OF JF1rel_def OO_Grp_alt]])


lemma in_JF2rel:
  "JF2rel R x y \<longleftrightarrow> (\<exists> z. z \<in> JF2in (Collect (case_prod R)) \<and> JF2map fst z = x \<and> JF2map snd z = y)"
  by (rule predicate2_eqD[OF trans[OF JF2rel_def OO_Grp_alt]])

lemma J_rel_coind_ind:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> F1in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F1map fst fst fst (f x y) = dtor1 x \<and>
                               F1map snd snd snd (f x y) = dtor1 y);
   \<forall>x y. R3 x y \<longrightarrow> (g x y \<in> F2in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F2map fst fst fst (g x y) = dtor2 x \<and>
                               F2map snd snd snd (g x y) = dtor2 y)\<rbrakk> \<Longrightarrow>
  (\<forall>a\<in>JF1set z1. \<forall>x y. R2 x y \<and> z1 = unfold1 (case_prod f) (case_prod g) (x, y) \<longrightarrow> R1 (fst a) (snd a)) \<and>
  (\<forall>a\<in>JF2set z2. \<forall>x y. R3 x y \<and> z2 = unfold2 (case_prod f) (case_prod g) (x, y) \<longrightarrow> R1 (fst a) (snd a))"
  apply (tactic \<open>rtac @{context} (rule_by_tactic @{context} (ALLGOALS (TRY o etac @{context} asm_rl))
  @{thm JFset_induct[of
  "\<lambda>a z1. \<forall>x y. R2 x y \<and> z1 = unfold1 (case_prod f) (case_prod g) (x, y) \<longrightarrow> R1 (fst a) (snd a)"
  "\<lambda>a z2. \<forall>x y. R3 x y \<and> z2 = unfold2 (case_prod f) (case_prod g) (x, y) \<longrightarrow> R1 (fst a) (snd a)"
  z1 z2]}) 1\<close>)
       apply (rule allI impI)+
       apply (erule conjE)
       apply (drule spec2)
       apply (erule thin_rl)
       apply (drule mp)
        apply assumption
       apply (erule CollectE conjE Collect_case_prodD[OF subsetD] rev_subsetD)+
       apply hypsubst
  unfolding unfold1 F1.set_map(1) prod.case image_id id_apply
       apply (rule subset_refl)

      apply (rule allI impI)+
      apply (erule conjE)
      apply (erule thin_rl)
      apply (drule spec2)
      apply (drule mp)
       apply assumption
      apply (erule CollectE conjE Collect_case_prodD[OF subsetD] rev_subsetD)+
      apply hypsubst
  unfolding unfold2 F2.set_map(1) prod.case image_id id_apply
      apply (rule subset_refl)

(**)

     apply (rule impI allI)+
     apply (erule conjE)
     apply (drule spec2)
     apply (erule thin_rl)
     apply (drule mp)
      apply assumption
     apply (erule CollectE conjE)+
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding unfold1 F1.set_map(2) prod.case image_id id_apply
     apply (erule imageE)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (erule allE mp)+
     apply (rule conjI)
      apply (erule Collect_case_prodD[OF subsetD])
      apply assumption
     apply (rule arg_cong[OF surjective_pairing])
    (**)

    apply (rule impI allI)+
    apply (erule conjE)
    apply (drule spec2)
    apply (erule thin_rl)
    apply (drule mp)
     apply assumption
    apply (erule CollectE conjE)+
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding unfold1 F1.set_map(3) prod.case image_id id_apply
    apply (erule imageE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (erule allE mp)+
    apply (rule conjI)
     apply (erule Collect_case_prodD[OF subsetD])
     apply assumption
    apply (rule arg_cong[OF surjective_pairing])

(**)

   apply (rule impI allI)+
   apply (erule conjE)
   apply (erule thin_rl)
   apply (drule spec2)
   apply (drule mp)
    apply assumption
   apply (erule CollectE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding unfold2 F2.set_map(2) prod.case image_id id_apply
   apply (erule imageE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule allE mp)+
   apply (rule conjI)
    apply (erule Collect_case_prodD[OF subsetD])
    apply assumption
   apply (rule arg_cong[OF surjective_pairing])
    (**)

  apply (rule impI allI)+
  apply (erule conjE)
  apply (erule thin_rl)
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding unfold2 F2.set_map(3) prod.case image_id id_apply
  apply (erule imageE)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule allE mp)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind_coind1:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> F1in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F1map fst fst fst (f x y) = dtor1 x \<and>
                               F1map snd snd snd (f x y) = dtor1 y);
   \<forall>x y. R3 x y \<longrightarrow> (g x y \<in> F2in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F2map fst fst fst (g x y) = dtor2 x \<and>
                               F2map snd snd snd (g x y) = dtor2 y)\<rbrakk> \<Longrightarrow>
  ((\<exists>y. R2 x1 y \<and> x1' = JF1map fst (unfold1 (case_prod f) (case_prod g) (x1, y))) \<longrightarrow> x1' = x1) \<and>
  ((\<exists>y. R3 x2 y \<and> x2' = JF2map fst (unfold2 (case_prod f) (case_prod g) (x2, y))) \<longrightarrow> x2' = x2)"
  apply (rule Frel_coind[of
        "\<lambda>x1' x1. \<exists>y. R2 x1 y \<and> x1' = JF1map fst (unfold1 (case_prod f) (case_prod g) (x1, y))"
        "\<lambda>x2' x2. \<exists>y. R3 x2 y \<and> x2' = JF2map fst (unfold2 (case_prod f) (case_prod g) (x2, y))"
        x1' x1
        x2' x2
        ])
   apply (intro allI impI iffD2[OF F1.in_rel])

   apply (erule exE conjE)+
   apply (drule spec2)
   apply (erule thin_rl)
   apply (drule mp)
    apply assumption
   apply (erule CollectE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule exI)
   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans[OF F1.map_comp])
     apply (rule sym[OF trans[OF JF1map_simps]])
     apply (rule trans[OF arg_cong[OF unfold1]])
     apply (rule trans[OF F1.map_comp F1.map_cong0])
       apply (rule trans[OF fun_cong[OF o_id]])
       apply (rule sym[OF fun_cong[OF fst_diag_fst]])
      apply (rule sym[OF trans[OF o_apply]])
      apply (rule fst_conv)
     apply (rule sym[OF trans[OF o_apply]])
     apply (rule fst_conv)
    apply (rule trans[OF F1.map_comp])
    apply (rule trans[OF F1.map_cong0])
       apply (rule fun_cong[OF snd_diag_fst])
      apply (rule trans[OF o_apply])
      apply (rule snd_conv)
     apply (rule trans[OF o_apply])
     apply (rule snd_conv)
    apply (erule trans[OF arg_cong[OF prod.case]])

   apply (unfold prod.case o_def fst_conv snd_conv) []
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(1)])
    apply (rule image_subsetI CollectI case_prodI)+
    apply (rule refl)

   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(2)])
    apply (rule image_subsetI CollectI case_prodI exI)+
    apply (rule conjI)
     apply (erule Collect_case_prodD[OF subsetD])
     apply assumption
    apply (rule arg_cong[OF surjective_pairing])

   apply (rule ord_eq_le_trans[OF F1.set_map(3)])
   apply (rule image_subsetI CollectI case_prodI exI)+
   apply (rule conjI)
    apply (erule Collect_case_prodD[OF subsetD])
    apply assumption
   apply (rule arg_cong[OF surjective_pairing])

(**)

  apply (intro allI impI iffD2[OF F2.in_rel])

  apply (erule exE conjE)+
  apply (erule thin_rl)
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule exI)
  apply (rule conjI[rotated])
   apply (rule conjI)
    apply (rule trans[OF F2.map_comp])
    apply (rule sym[OF trans[OF JF2map_simps]])
    apply (rule trans[OF arg_cong[OF unfold2]])
    apply (rule trans[OF F2.map_comp F2.map_cong0])
      apply (rule fun_cong[OF trans[OF o_id fst_diag_fst[symmetric]]])
     apply (rule sym[OF trans[OF o_apply]])
     apply (rule fst_conv)
    apply (rule sym[OF trans[OF o_apply]])
    apply (rule fst_conv)
   apply (rule trans[OF F2.map_comp])
   apply (rule trans[OF F2.map_cong0])
      apply (rule fun_cong[OF snd_diag_fst])
     apply (rule trans[OF o_apply])
     apply (rule snd_conv)
    apply (rule trans[OF o_apply])
    apply (rule snd_conv)
   apply (erule trans[OF arg_cong[OF prod.case]])

  apply (unfold prod.case o_def fst_conv snd_conv) []
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(1)])
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule case_prodI)
   apply (rule refl)

  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(2)])
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule case_prodI)
   apply (rule exI)
   apply (rule conjI)
    apply (erule Collect_case_prodD[OF subsetD])
    apply assumption
   apply (rule arg_cong[OF surjective_pairing])

  apply (rule ord_eq_le_trans[OF F2.set_map(3)])
  apply (rule image_subsetI CollectI case_prodI exI)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind_coind2:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> F1in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F1map fst fst fst (f x y) = dtor1 x \<and>
                               F1map snd snd snd (f x y) = dtor1 y);
   \<forall>x y. R3 x y \<longrightarrow> (g x y \<in> F2in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) \<and>
                               F2map fst fst fst (g x y) = dtor2 x \<and>
                               F2map snd snd snd (g x y) = dtor2 y)\<rbrakk> \<Longrightarrow>
  ((\<exists>x. R2 x y1 \<and> y1' = JF1map snd (unfold1 (case_prod f) (case_prod g) (x, y1))) \<longrightarrow> y1' = y1) \<and>
  ((\<exists>x. R3 x y2 \<and> y2' = JF2map snd (unfold2 (case_prod f) (case_prod g) (x, y2))) \<longrightarrow> y2' = y2)"
  apply (rule Frel_coind[of
        "\<lambda>y1' y1. \<exists>x. R2 x y1 \<and> y1' = JF1map snd (unfold1 (case_prod f) (case_prod g) (x, y1))"
        "\<lambda>y2' y2. \<exists>x. R3 x y2 \<and> y2' = JF2map snd (unfold2 (case_prod f) (case_prod g) (x, y2))"
        y1' y1
        y2' y2
        ])
   apply (intro allI impI iffD2[OF F1.in_rel])

   apply (erule exE conjE)+
   apply (drule spec2)
   apply (erule thin_rl)
   apply (drule mp)
    apply assumption
   apply (erule CollectE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule exI)
   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans[OF F1.map_comp])
     apply (rule sym[OF trans[OF JF1map_simps]])
     apply (rule trans[OF arg_cong[OF unfold1]])
     apply (rule trans[OF F1.map_comp F1.map_cong0])
       apply (rule trans[OF fun_cong[OF o_id]])
       apply (rule sym[OF fun_cong[OF fst_diag_snd]])
      apply (rule sym[OF trans[OF o_apply]])
      apply (rule fst_conv)
     apply (rule sym[OF trans[OF o_apply]])
     apply (rule fst_conv)
    apply (rule trans[OF F1.map_comp])
    apply (rule trans[OF F1.map_cong0])
       apply (rule fun_cong[OF snd_diag_snd])
      apply (rule trans[OF o_apply])
      apply (rule snd_conv)
     apply (rule trans[OF o_apply])
     apply (rule snd_conv)
    apply (erule trans[OF arg_cong[OF prod.case]])

   apply (unfold prod.case o_def fst_conv snd_conv) []
   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(1)])
    apply (rule image_subsetI CollectI case_prodI)+
    apply (rule refl)

   apply (rule conjI)
    apply (rule ord_eq_le_trans[OF F1.set_map(2)])
    apply (rule image_subsetI CollectI case_prodI exI)+
    apply (rule conjI)
     apply (erule Collect_case_prodD[OF subsetD])
     apply assumption
    apply (rule arg_cong[OF surjective_pairing])

   apply (rule ord_eq_le_trans[OF F1.set_map(3)])
   apply (rule image_subsetI CollectI case_prodI exI)+
   apply (rule conjI)
    apply (erule Collect_case_prodD[OF subsetD])
    apply assumption
   apply (rule arg_cong[OF surjective_pairing])

(**)

  apply (intro allI impI iffD2[OF F2.in_rel])

  apply (erule exE conjE)+
  apply (erule thin_rl)
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule exI)
  apply (rule conjI[rotated])
   apply (rule conjI)
    apply (rule trans[OF F2.map_comp])
    apply (rule sym[OF trans[OF JF2map_simps]])
    apply (rule trans[OF arg_cong[OF unfold2]])
    apply (rule trans[OF F2.map_comp F2.map_cong0])
      apply (rule trans[OF fun_cong[OF o_id]])
      apply (rule sym[OF fun_cong[OF fst_diag_snd]])
     apply (rule sym[OF trans[OF o_apply]])
     apply (rule fst_conv)
    apply (rule sym[OF trans[OF o_apply]])
    apply (rule fst_conv)
   apply (rule trans[OF F2.map_comp])
   apply (rule trans[OF F2.map_cong0])
      apply (rule fun_cong[OF snd_diag_snd])
     apply (rule trans[OF o_apply])
     apply (rule snd_conv)
    apply (rule trans[OF o_apply])
    apply (rule snd_conv)
   apply (erule trans[OF arg_cong[OF prod.case]])

  apply (unfold prod.case o_def fst_conv snd_conv) []
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(1)])
   apply (rule image_subsetI CollectI case_prodI)+
   apply (rule refl)

  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F2.set_map(2)])
   apply (rule image_subsetI CollectI case_prodI exI)+
   apply (rule conjI)
    apply (erule Collect_case_prodD[OF subsetD])
    apply assumption
   apply (rule arg_cong[OF surjective_pairing])

  apply (rule ord_eq_le_trans[OF F2.set_map(3)])
  apply (rule image_subsetI CollectI case_prodI exI)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind:
  assumes CIH1: "\<forall>x2 y2. R2 x2 y2 \<longrightarrow> F1rel R1 R2 R3 (dtor1 x2) (dtor1 y2)"
    and     CIH2: "\<forall>x3 y3. R3 x3 y3 \<longrightarrow> F2rel R1 R2 R3 (dtor2 x3) (dtor2 y3)"
  shows   "R2 \<le> JF1rel R1 \<and> R3 \<le> JF2rel R1"
  apply (insert CIH1 CIH2)
  unfolding F1.in_rel F2.in_rel ex_simps(6)[symmetric] choice_iff
  apply (erule exE)+
  apply (rule conjI)

   apply (rule predicate2I)
   apply (rule iffD2[OF in_JF1rel])
   apply (rule exI conjI)+
    apply (rule CollectI)
    apply (rule rev_mp[OF conjunct1[OF J_rel_coind_ind]])
      apply assumption
     apply assumption
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (rule impI)
    apply (rule subsetI CollectI iffD2[OF case_prod_beta])+
    apply (drule bspec)
     apply assumption
    apply (erule allE mp conjE)+
    apply (erule conjI[OF _ refl])

   apply (rule conjI)
    apply (rule rev_mp[OF conjunct1[OF J_rel_coind_coind1]])
      apply assumption
     apply assumption
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (rule impI)
    apply (erule mp)
    apply (rule exI)
    apply (erule conjI[OF _ refl])

   apply (rule rev_mp[OF conjunct1[OF J_rel_coind_coind2]])
     apply assumption
    apply assumption
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (rule impI)
   apply (erule mp)
   apply (rule exI)
   apply (erule conjI[OF _ refl])

(**)

  apply (rule predicate2I)
  apply (rule iffD2[OF in_JF2rel])
  apply (rule exI conjI)+
   apply (rule rev_mp[OF conjunct2[OF J_rel_coind_ind]])
     apply assumption
    apply assumption
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (rule impI)
   apply (rule CollectI)
   apply (rule subsetI CollectI iffD2[OF case_prod_beta])+
   apply (drule bspec)
    apply assumption
   apply (erule allE mp conjE)+
   apply (erule conjI[OF _ refl])

  apply (rule conjI)
   apply (rule rev_mp[OF conjunct2[OF J_rel_coind_coind1]])
     apply assumption
    apply assumption
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (rule impI)
   apply (erule mp)
   apply (rule exI)
   apply (erule conjI[OF _ refl])

  apply (rule rev_mp[OF conjunct2[OF J_rel_coind_coind2]])
    apply assumption
   apply assumption
  apply (erule thin_rl)
  apply (erule thin_rl)
  apply (rule impI)
  apply (erule mp)
  apply (rule exI)
  apply (erule conjI[OF _ refl])
  done

lemma JF1rel_F1rel: "JF1rel R a b \<longleftrightarrow> F1rel R (JF1rel R) (JF2rel R) (dtor1 a) (dtor1 b)"
  apply (rule iffI)
   apply (drule iffD1[OF in_JF1rel])
   apply (erule exE conjE CollectE)+
   apply (rule iffD2[OF F1.in_rel])
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (erule subset_trans[OF F1set1_incl_JF1set])

    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F1.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule iffD2[OF in_JF1rel])
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (erule subset_trans[OF F1set2_JF1set_incl_JF1set])
      apply assumption
     apply (rule conjI)
      apply (rule refl)
     apply (rule refl)

    apply (rule ord_eq_le_trans)
     apply (rule F1.set_map(3))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule iffD2[OF in_JF2rel])
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (erule subset_trans[OF F1set3_JF2set_incl_JF1set])
     apply assumption
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
    apply (rule trans)
     apply (rule sym)
     apply (rule JF1map_simps)
    apply (rule iffD2[OF dtor1_diff])
    apply assumption

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
   apply (rule trans)
    apply (rule sym)
    apply (rule JF1map_simps)
   apply (rule iffD2[OF dtor1_diff])
   apply assumption

  apply (drule iffD1[OF F1.in_rel])
  apply (erule exE conjE CollectE)+
  apply (rule iffD2[OF in_JF1rel])
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule JF1set_simps)
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule box_equals)
       apply (rule F1.set_map(1))
      apply (rule arg_cong[OF sym[OF dtor1_ctor1]])
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule SUP_cong[OF _ refl])
     apply (rule box_equals[OF _ _ refl])
      apply (rule F1.set_map(2))
     apply (rule arg_cong[OF sym[OF dtor1_ctor1]])
    apply (rule UN_least)
    apply (drule rev_subsetD)
     apply (erule image_mono)
    apply (erule imageE)
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (drule iffD1[OF in_JF1rel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply (erule CollectE conjE)+
    apply assumption

   apply (rule ord_eq_le_trans)
    apply (rule trans[OF arg_cong[OF dtor1_ctor1]])
    apply (rule arg_cong[OF F1.set_map(3)])
   apply (rule UN_least)
   apply (drule rev_subsetD)
    apply (erule image_mono)
   apply (erule imageE)
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (drule iffD1[OF in_JF2rel])
   apply (drule someI_ex)
   apply (erule exE conjE)+
   apply (erule CollectD)

  apply (rule conjI)

   apply (rule iffD1[OF dtor1_diff])
   apply (rule trans)
    apply (rule JF1map_simps)
   apply (rule box_equals)
     apply (rule F1.map_comp)
    apply (rule arg_cong[OF sym[OF dtor1_ctor1]])
   apply (rule trans)
    apply (rule F1.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans[OF o_apply])
     apply (drule rev_subsetD)
      apply assumption
     apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
     apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
     apply hypsubst
     apply (drule iffD1[OF in_JF1rel])
     apply (drule someI_ex)
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (drule iffD1[OF in_JF2rel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply assumption

  apply (rule iffD1[OF dtor1_diff])
  apply (rule trans)
   apply (rule JF1map_simps)
  apply (rule trans)
   apply (rule arg_cong[OF dtor1_ctor1])
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
    apply (drule iffD1[OF in_JF1rel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply (rule trans[OF o_apply])
   apply (drule rev_subsetD)
    apply assumption
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (drule iffD1[OF in_JF2rel])
   apply (drule someI_ex)
   apply (erule conjE)+
   apply assumption
  apply assumption
  done

lemma JF2rel_F2rel: "JF2rel R a b \<longleftrightarrow> F2rel R (JF1rel R) (JF2rel R) (dtor2 a) (dtor2 b)"
  apply (rule iffI)
   apply (drule iffD1[OF in_JF2rel])
   apply (erule exE conjE CollectE)+
   apply (rule iffD2[OF F2.in_rel])
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F2.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (rule subset_trans)
      apply (rule F2set1_incl_JF2set)
     apply assumption

    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F2.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule iffD2[OF in_JF1rel])
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (rule subset_trans)
       apply (rule F2set2_JF1set_incl_JF2set)
       apply assumption
      apply assumption
     apply (rule conjI)
      apply (rule refl)
     apply (rule refl)

    apply (rule ord_eq_le_trans)
     apply (rule F2.set_map(3))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule iffD2[OF in_JF2rel])
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (rule subset_trans)
      apply (rule F2set3_JF2set_incl_JF2set)
      apply assumption
     apply assumption
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
    apply (rule trans)
     apply (rule sym)
     apply (rule JF2map_simps)
    apply (rule iffD2)
     apply (rule dtor2_diff)
    apply assumption

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
   apply (rule trans)
    apply (rule sym)
    apply (rule JF2map_simps)
   apply (rule iffD2)
    apply (rule dtor2_diff)
   apply assumption

  apply (drule iffD1[OF F2.in_rel])
  apply (erule exE conjE CollectE)+
  apply (rule iffD2[OF in_JF2rel])
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule JF2set_simps)
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
    apply hypsubst
    apply (drule iffD1[OF in_JF1rel])
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
   apply (drule iffD1[OF in_JF2rel])
   apply (drule someI_ex)
   apply (erule exE conjE)+
   apply (erule CollectD)

  apply (rule conjI)

   apply (rule iffD1)
    apply (rule dtor2_diff)
   apply (rule trans)
    apply (rule JF2map_simps)
   apply (rule trans)
    apply (rule arg_cong[OF dtor2_ctor2])
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
     apply (drule iffD1[OF in_JF1rel])
     apply (drule someI_ex)
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (drule iffD1[OF in_JF2rel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply assumption

  apply (rule iffD1)
   apply (rule dtor2_diff)
  apply (rule trans)
   apply (rule JF2map_simps)
  apply (rule trans)
   apply (rule arg_cong[OF dtor2_ctor2])
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
    apply (drule iffD1[OF in_JF1rel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply (rule trans[OF o_apply])
   apply (drule rev_subsetD)
    apply assumption
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (drule iffD1[OF in_JF2rel])
   apply (drule someI_ex)
   apply (erule conjE)+
   apply assumption
  apply assumption
  done

lemma JFrel_Comp_le:
  "JF1rel R1 OO JF1rel R2 \<le> JF1rel (R1 OO R2) \<and> JF2rel R1 OO JF2rel R2 \<le> JF2rel (R1 OO R2)"
  apply (rule J_rel_coind[OF allI[OF allI[OF impI]] allI[OF allI[OF impI]]])
   apply (rule predicate2D[OF eq_refl[OF sym[OF F1.rel_compp]]])
   apply (erule relcomppE)
   apply (rule relcomppI)
    apply (erule iffD1[OF JF1rel_F1rel])
   apply (erule iffD1[OF JF1rel_F1rel])
  apply (rule predicate2D[OF eq_refl[OF sym[OF F2.rel_compp]]])
  apply (erule relcomppE)
  apply (rule relcomppI)
   apply (erule iffD1[OF JF2rel_F2rel])
  apply (erule iffD1[OF JF2rel_F2rel])
  done

context includes lifting_syntax
begin

lemma unfold_transfer:
  "((S ===> F1rel R S T) ===> (T ===> F2rel R S T) ===> S ===> JF1rel R) unfold1 unfold1 \<and>
  ((S ===> F1rel R S T) ===> (T ===> F2rel R S T) ===> T ===> JF2rel R) unfold2 unfold2"
  unfolding rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]
  unfolding rel_fun_iff_geq_image2p
  apply (rule allI impI)+
  apply (rule J_rel_coind)
   apply (rule allI impI)+
   apply (erule image2pE)
   apply hypsubst
   apply (unfold unfold1 unfold2) [1]
   apply (rule rel_funD[OF rel_funD[OF rel_funD[OF rel_funD[OF F1.map_transfer]]]])
      apply (rule id_transfer)
     apply (rule rel_fun_image2p)
    apply (rule rel_fun_image2p)
   apply (erule predicate2D)
   apply (erule image2pI)

  apply (rule allI impI)+
  apply (erule image2pE)
  apply hypsubst
  apply (unfold unfold1 unfold2) [1]
  apply (rule rel_funD[OF rel_funD[OF rel_funD[OF rel_funD[OF F2.map_transfer]]]])
     apply (rule id_transfer)
    apply (rule rel_fun_image2p)
   apply (rule rel_fun_image2p)
  apply (erule predicate2D)
  apply (erule image2pI)
  done

end

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Greatest_FP false 1 @{thm unfold_unique}
    @{thms JF1map JF2map} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms unfold1 unfold2})
    @{thms F1.map_comp0[symmetric] F2.map_comp0[symmetric]} @{thms F1.map_cong0 F2.map_cong0}
\<close>

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Greatest_FP true 1 @{thm corec_unique}
    @{thms JF1map JF2map} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms corec1 corec2})
    @{thms F1.map_comp0[symmetric] F2.map_comp0[symmetric]} @{thms F1.map_cong0 F2.map_cong0}
\<close>

bnf "'a JF1"
  map: JF1map
  sets: JF1set
  bd: bd_F
  wits: JF1wit
  rel: JF1rel
           apply -
           apply (rule JF1map_id)
          apply (rule JF1map_comp)
         apply (erule JF1map_cong0[OF ballI])
        apply (rule JF1set_natural)
       apply (rule bd_F_card_order)
      apply (rule conjunct1[OF bd_F_Cinfinite])
     apply (rule JF1set_bd)
    apply (rule conjunct1[OF JFrel_Comp_le])
   apply (rule JF1rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule JF1wit)
  done

bnf "'a JF2"
  map: JF2map
  sets: JF2set
  bd: bd_F
  wits: JF2wit
  rel: JF2rel
           apply -
           apply (rule JF2map_id)
          apply (rule JF2map_comp)
         apply (erule JF2map_cong0[OF ballI])
        apply (rule JF2set_natural)
       apply (rule bd_F_card_order)
      apply (rule conjunct1[OF bd_F_Cinfinite])
     apply (rule JF2set_bd)
    apply (rule conjunct2[OF JFrel_Comp_le])
   apply (rule JF2rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule JF2wit)
  done

(*<*)
end
(*>*)
