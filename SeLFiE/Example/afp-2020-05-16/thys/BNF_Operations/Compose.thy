(*  Title:       Compose
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Normalized Composition of BNFs\<close>

text \<open>Expected normal form: outer m-ary BNF is composed with m inner n-ary BNFs.\<close>

(*<*)
theory Compose
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

declare [[bnf_internals]]
bnf_axiomatization (dead 'p1, F1set1: 'a1, F1set2: 'a2) F1
  [wits: "('p1, 'a1, 'a2) F1"]
  for map: F1map rel: F1rel
bnf_axiomatization (dead 'p2, F2set1: 'a1, F2set2: 'a2) F2
  [wits: "'a1 \<Rightarrow> ('p2, 'a1, 'a2) F2" "'a2 \<Rightarrow> ('p2, 'a1, 'a2) F2"]
  for map: F2map rel: F2rel
bnf_axiomatization (dead 'p3, F3set1: 'a1, F3set2: 'a2) F3
  [wits: "'a1 \<Rightarrow> 'a2 \<Rightarrow> ('p3, 'a1, 'a2) F3"]
  for map: F3map rel: F3rel
bnf_axiomatization (dead 'p, Gset1: 'b1, Gset2: 'b2, Gset3: 'b3) G
  [wits: "'b1 \<Rightarrow> 'b3 \<Rightarrow> ('p, 'b1, 'b2, 'b3) G" "'b2 \<Rightarrow> 'b3 \<Rightarrow> ('p, 'b1, 'b2, 'b3) G"]
  for map: Gmap rel: Grel
type_synonym ('p1, 'p2, 'p3, 'p, 'a1, 'a2) H =
  "('p, ('p1, 'a1, 'a2) F1, ('p2, 'a1, 'a2) F2, ('p3, 'a1, 'a2) F3) G"
type_synonym ('p1, 'p2, 'p3, 'p) Hbd_type =
  "('p1 bd_type_F1 + 'p2 bd_type_F2 + 'p3 bd_type_F3) \<times> 'p bd_type_G"

abbreviation F1in where "F1in A1 A2 \<equiv> {x. F1set1 x \<subseteq> A1 \<and> F1set2 x \<subseteq> A2}"
abbreviation F2in where "F2in A1 A2 \<equiv> {x. F2set1 x \<subseteq> A1 \<and> F2set2 x \<subseteq> A2}"
abbreviation F3in where "F3in A1 A2 \<equiv> {x. F3set1 x \<subseteq> A1 \<and> F3set2 x \<subseteq> A2}"
abbreviation Gin where "Gin A1 A2 A3 \<equiv> {x. Gset1 x \<subseteq> A1 \<and> Gset2 x \<subseteq> A2 \<and> Gset3 x \<subseteq> A3}"

abbreviation Gset where
  "Gset \<equiv> BNF_Def.collect {Gset1, Gset2, Gset3}"

abbreviation Hmap :: "('a1 \<Rightarrow> 'b1) \<Rightarrow> ('a2 \<Rightarrow> 'b2) \<Rightarrow>
  ('p1, 'p2, 'p3, 'p, 'a1, 'a2) H \<Rightarrow> ('p1, 'p2, 'p3, 'p, 'b1, 'b2) H" where
  "Hmap f g \<equiv> Gmap (F1map f g) (F2map f g) (F3map f g)"

abbreviation Hset1 :: "('p1, 'p2, 'p3, 'p, 'a1, 'a2) H \<Rightarrow> 'a1 set" where
  "Hset1 \<equiv> Union o Gset o Gmap F1set1 F2set1 F3set1"

abbreviation Hset2 :: "('p1, 'p2, 'p3, 'p, 'a1, 'a2) H \<Rightarrow> 'a2 set" where
  "Hset2 \<equiv> Union o Gset o Gmap F1set2 F2set2 F3set2"

lemma Hset1_alt:
  "Hset1 = Union o BNF_Def.collect {image F1set1 o Gset1, image F2set1 o Gset2, image F3set1 o Gset3}"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_alt_tac @{context} @{thm G.collect_set_map}\<close>)

lemma Hset2_alt:
  "Hset2 = Union o BNF_Def.collect {image F1set2 o Gset1, image F2set2 o Gset2, image F3set2 o Gset3}"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_alt_tac @{context} @{thm G.collect_set_map}\<close>)

abbreviation Hbd where
  "Hbd \<equiv> (bd_F1 +c bd_F2 +c bd_F3) *c bd_G"

theorem Hmap_id: "Hmap id id = id"
  unfolding G.map_id0 F1.map_id0 F2.map_id0 F3.map_id0 ..

theorem Hmap_comp: "Hmap (f1 o g1) (f2 o g2) = Hmap f1 f2 o Hmap g1 g2"
  unfolding G.map_comp0 F1.map_comp0 F2.map_comp0 F3.map_comp0 ..

theorem Hmap_cong: "\<lbrakk>\<And>z. z \<in> Hset1 x \<Longrightarrow> f1 z = g1 z; \<And>z. z \<in> Hset2 x \<Longrightarrow> f2 z = g2 z\<rbrakk> \<Longrightarrow>
  Hmap f1 f2 x = Hmap g1 g2 x"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_map_cong0_tac @{context}
  [] @{thms Hset1_alt Hset2_alt} @{thm G.map_cong0} @{thms F1.map_cong0 F2.map_cong0 F3.map_cong0}\<close>)

theorem Hset1_natural: "Hset1 o Hmap f1 f2 = image f1 o Hset1"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_map0_tac @{context} @{thm refl} @{thm G.map_comp0} @{thm G.map_cong0}
  @{thm G.collect_set_map} @{thms F1.set_map0(1) F2.set_map0(1) F3.set_map0(1)}\<close>)

theorem Hset2_natural: "Hset2 o Hmap f1 f2 = image f2 o Hset2"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_map0_tac @{context} @{thm refl} @{thm G.map_comp0} @{thm G.map_cong0}
  @{thm G.collect_set_map} @{thms F1.set_map0(2) F2.set_map0(2) F3.set_map0(2)}\<close>)

theorem Hbd_card_order: "card_order Hbd"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_bd_card_order_tac @{context}
  @{thms F1.bd_card_order F2.bd_card_order F3.bd_card_order} @{thm G.bd_card_order}\<close>)

theorem Hbd_cinfinite: "cinfinite Hbd"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_bd_cinfinite_tac @{context}
  @{thm F1.bd_cinfinite} @{thm G.bd_cinfinite}\<close>)

theorem Hset1_bd: "|Hset1 (x :: ('p1, 'p2, 'p3, 'p, 'a1, 'a2) H )| \<le>o
  (Hbd :: ('p1, 'p2, 'p3, 'p) Hbd_type rel)"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_bd_tac @{context} @{thm refl} NONE @{thm Hset1_alt}
      @{thms comp_single_set_bd[OF F1.bd_Card_order F1.set_bd(1) G.set_bd(1)]
             comp_single_set_bd[OF F2.bd_Card_order F2.set_bd(1) G.set_bd(2)]
             comp_single_set_bd[OF F3.bd_Card_order F3.set_bd(1) G.set_bd(3)]}\<close>)

theorem Hset2_bd: "|Hset2 (x :: ('p1, 'p2, 'p3, 'p, 'a1, 'a2) H )| \<le>o
  (Hbd :: ('p1, 'p2, 'p3, 'p) Hbd_type rel)"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_set_bd_tac @{context} @{thm refl} NONE @{thm Hset2_alt}
      @{thms comp_single_set_bd[OF F1.bd_Card_order F1.set_bd(2) G.set_bd(1)]
             comp_single_set_bd[OF F2.bd_Card_order F2.set_bd(2) G.set_bd(2)]
             comp_single_set_bd[OF F3.bd_Card_order F3.set_bd(2) G.set_bd(3)]}\<close>)

abbreviation Hin where "Hin A1 A2 \<equiv> {x. Hset1 x \<subseteq> A1 \<and> Hset2 x \<subseteq> A2}"

lemma Hin_alt: "Hin A1 A2 = Gin (F1in A1 A2) (F2in A1 A2) (F3in A1 A2)"
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_in_alt_tac @{context} @{thms Hset1_alt Hset2_alt}\<close>)

definition Hwit1 where "Hwit1 b c = wit1_G wit_F1 (wit_F3 b c)"
definition Hwit21 where "Hwit21 b c = wit2_G (wit1_F2 b) (wit_F3 b c)"
definition Hwit22 where "Hwit22 b c = wit2_G (wit2_F2 c) (wit_F3 b c)"

lemma Hwit1:
  "\<And>x. x \<in> Hset1 (Hwit1 b c) \<Longrightarrow> x = b"
  "\<And>x. x \<in> Hset2 (Hwit1 b c) \<Longrightarrow> x = c"
  unfolding Hwit1_def
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_wit_tac @{context} [] @{thms G.wit1 G.wit2}
  @{thm G.collect_set_map} @{thms F1.wit F2.wit1 F2.wit2 F3.wit}\<close>)

lemma Hwit21:
  "\<And>x. x \<in> Hset1 (Hwit21 b c) \<Longrightarrow> x = b"
  "\<And>x. x \<in> Hset2 (Hwit21 b c) \<Longrightarrow> x = c"
  unfolding Hwit21_def
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_wit_tac @{context} [] @{thms G.wit1 G.wit2}
  @{thm G.collect_set_map} @{thms F1.wit F2.wit1 F2.wit2 F3.wit}\<close>)


lemma Hwit22:
  "\<And>x. x \<in> Hset1 (Hwit22 b c) \<Longrightarrow> x = b"
  "\<And>x. x \<in> Hset2 (Hwit22 b c) \<Longrightarrow> x = c"
  unfolding Hwit22_def
  by (tactic \<open>BNF_Comp_Tactics.mk_comp_wit_tac @{context} [] @{thms G.wit1 G.wit2}
  @{thm G.collect_set_map} @{thms F1.wit F2.wit1 F2.wit2 F3.wit}\<close>)

(* Relator structure for H *)

lemma Grel_cong: "\<lbrakk>R1 = S1; R2 = S2; R3 = S3\<rbrakk> \<Longrightarrow> Grel R1 R2 R3 = Grel S1 S2 S3"
  by hypsubst (rule refl)

definition Hrel where
  "Hrel R1 R2 = (BNF_Def.Grp (Hin (Collect (case_prod R1)) (Collect (case_prod R2))) (Hmap fst fst))^--1 OO
                (BNF_Def.Grp (Hin (Collect (case_prod R1)) (Collect (case_prod R2))) (Hmap snd snd))"

lemmas Hrel_unfold = trans[OF Hrel_def trans[OF OO_Grp_cong[OF Hin_alt]
      trans[OF arg_cong2[of _ _ _ _ relcompp, OF trans[OF arg_cong[of _ _ conversep, OF sym[OF G.rel_Grp]] G.rel_conversep[symmetric]] sym[OF G.rel_Grp]]
        trans[OF G.rel_compp[symmetric] Grel_cong[OF sym[OF F1.rel_compp_Grp] sym[OF F2.rel_compp_Grp] sym[OF F3.rel_compp_Grp]]]]]]

bnf H: "('p1, 'p2, 'p3, 'p, 'a1, 'a2) H"
  map: Hmap
  sets: Hset1 Hset2
  bd: "Hbd :: ('p1, 'p2, 'p3, 'p) Hbd_type rel"
  rel: Hrel
            apply -
            apply (rule Hmap_id)
           apply (rule Hmap_comp)
          apply (erule Hmap_cong) apply assumption
         apply (rule Hset1_natural)
        apply (rule Hset2_natural)
       apply (rule Hbd_card_order)
      apply (rule Hbd_cinfinite)
     apply (rule Hset1_bd)
    apply (rule Hset2_bd)
   apply (unfold Hrel_unfold G.rel_compp[symmetric] F1.rel_compp[symmetric] F2.rel_compp[symmetric] F3.rel_compp[symmetric] eq_OO) [1] apply (rule order_refl)
  apply (rule Hrel_def[unfolded OO_Grp_alt mem_Collect_eq])
  done

(*<*)
end
(*>*)
