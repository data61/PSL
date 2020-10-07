(*  Title:       Lift
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Adding New Live Variables\<close>

(*<*)
theory Lift
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

declare [[bnf_internals]]
bnf_axiomatization (dead 'p, Fset1: 'a1, Fset2: 'a2) F
  [wits: "'a1 \<Rightarrow> 'a2 \<Rightarrow> ('p, 'a1, 'a2) F"]
  for map: Fmap rel: Frel
type_synonym ('p, 'a1, 'a2, 'a3, 'a4) F' = "('p, 'a3, 'a4) F"

abbreviation F'map :: "('a1 \<Rightarrow> 'b1) \<Rightarrow> ('a2 \<Rightarrow> 'b2) \<Rightarrow> ('a3 \<Rightarrow> 'b3) \<Rightarrow> ('a4 \<Rightarrow> 'b4) \<Rightarrow> ('p, 'a1, 'a2, 'a3, 'a4) F' \<Rightarrow> ('p, 'b1, 'b2, 'b3, 'b4) F'" where
  "F'map f1 f2 f3 f4 \<equiv> Fmap f3 f4"

abbreviation F'set1 :: "('p, 'a1, 'a2, 'a3, 'a4) F' \<Rightarrow> 'a1 set" where
  "F'set1 \<equiv> \<lambda>_. {}"

abbreviation F'set2 :: "('p, 'a1, 'a2, 'a3, 'a4) F' \<Rightarrow> 'a2 set" where
  "F'set2 \<equiv> \<lambda>_. {}"

abbreviation F'set3 :: "('p, 'a1, 'a2, 'a3, 'a4) F' \<Rightarrow> 'a3 set" where
  "F'set3 \<equiv> Fset1"

abbreviation F'set4 :: "('p, 'a1, 'a2, 'a3, 'a4) F' \<Rightarrow> 'a4 set" where
  "F'set4 \<equiv> Fset2"

abbreviation F'bd where
  "F'bd \<equiv> bd_F"

theorem F'map_id: "F'map id id id id = id"
  by (rule F.map_id0)

theorem F'map_comp:
  "F'map (f1 o g1) (f2 o g2) (f3 o g3) (f4 o g4) = F'map f1 f2 f3 f4 o F'map g1 g2 g3 g4"
  by (rule F.map_comp0)

theorem F'map_cong:
  "\<lbrakk>\<And>z. z \<in> F'set1 x \<Longrightarrow> f1 z = g1 z; \<And>z. z \<in> F'set2 x \<Longrightarrow> f2 z = g2 z;
   \<And>z. z \<in> F'set3 x \<Longrightarrow> f3 z = g3 z; \<And>z. z \<in> F'set4 x \<Longrightarrow> f4 z = g4 z\<rbrakk>
  \<Longrightarrow> F'map f1 f2 f3 f4 x = F'map g1 g2 g3 g4 x"
  apply (tactic \<open>BNF_Util.rtac @{context} @{thm F.map_cong0} 1 THEN REPEAT_DETERM_N 2 (assume_tac @{context} 1)\<close>)
   apply assumption+
  done

theorem F'set1_natural: "F'set1 o F'map f1 f2 f3 f4 = image f1 o F'set1"
  by (tactic \<open>BNF_Comp_Tactics.empty_natural_tac @{context}\<close>)

theorem F'set2_natural: "F'set2 o F'map f1 f2 f3 f4 = image f2 o F'set2"
  by (tactic \<open>BNF_Comp_Tactics.empty_natural_tac @{context}\<close>)

theorem F'set3_natural: "F'set3 o F'map f1 f2 f3 f4 = image f3 o F'set3"
  by (rule F.set_map0(1))

theorem F'set4_natural: "F'set4 o F'map f1 f2 f3 f4 = image f4 o F'set4"
  by (rule F.set_map0(2))

theorem F'bd_card_order: "card_order bd_F"
  by (rule F.bd_card_order)

theorem F'bd_cinfinite: "cinfinite bd_F"
  by (rule F.bd_cinfinite)

theorem F'set1_bd: "|F'set1 x| \<le>o F'bd"
  by (tactic \<open>BNF_Comp_Tactics.mk_lift_set_bd_tac @{context} @{thm F.bd_Card_order}\<close>)

theorem F'set2_bd: "|F'set2 x| \<le>o F'bd"
  by (tactic \<open>BNF_Comp_Tactics.mk_lift_set_bd_tac @{context} @{thm F.bd_Card_order}\<close>)

theorem F'set3_bd: "|F'set3 (x :: ('c, 'a, 'd) F)| \<le>o (F'bd :: 'c bd_type_F rel)"
  by (rule F.set_bd(1))

theorem F'set4_bd: "|F'set4 (x :: ('c, 'a, 'd) F)| \<le>o (F'bd :: 'c bd_type_F rel)"
  by (rule F.set_bd(2))

abbreviation F'in :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> 'a4 set \<Rightarrow> (('p, 'a1, 'a2, 'a3, 'a4) F') set" where
  "F'in A1 A2 A3 A4 \<equiv> {x. F'set1 x \<subseteq> A1 \<and> F'set2 x \<subseteq> A2 \<and> F'set3 x \<subseteq> A3 \<and> F'set4 x \<subseteq> A4}"

definition F'rel where
  "F'rel R1 R2 R3 R4 = (BNF_Def.Grp (F'in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) (Collect (case_prod R4))) (F'map fst fst fst fst))^--1 OO
                      (BNF_Def.Grp (F'in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3)) (Collect (case_prod R4))) (F'map snd snd snd snd))"

lemmas F'rel_unfold = trans[OF F'rel_def[unfolded eqTrueI[OF empty_subsetI] simp_thms(22)]
    trans[OF OO_Grp_cong[OF refl] sym[OF F.rel_compp_Grp]]]

bnf F': "('p, 'a1, 'a2, 'a3, 'a4) F'"
  map: F'map
  sets: F'set1 F'set2 F'set3 F'set4
  bd: "F'bd :: 'p bd_type_F rel"
  wits: wit_F
  rel: F'rel
  plugins del: lifting transfer
  apply -
  apply (rule F'map_id)
  apply (rule F'map_comp)
  apply (erule F'map_cong) apply assumption+
  apply (rule F'set1_natural)
  apply (rule F'set2_natural)
  apply (rule F'set3_natural)
  apply (rule F'set4_natural)
  apply (rule F'bd_card_order)
  apply (rule F'bd_cinfinite)
  apply (rule F'set1_bd)
  apply (rule F'set2_bd)
  apply (rule F'set3_bd)
  apply (rule F'set4_bd)
  apply (unfold F'rel_unfold F.rel_compp[symmetric] eq_OO) [1] apply (rule order_refl)
  apply (rule F'rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule F.wit emptyE)+
  done

(*<*)
end
(*>*)
