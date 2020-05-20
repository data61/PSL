(*  Title:       Permute
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Changing the Order of Live Variables\<close>

(*<*)
theory Permute
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

declare [[bnf_internals]]
bnf_axiomatization (dead 'p, Fset1: 'a1, Fset2: 'a2, Fset3: 'a3) F for map: Fmap rel: Frel
type_synonym ('p, 'a1, 'a2, 'a3) F' = "('p, 'a3, 'a1, 'a2) F"

abbreviation Fin :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('p, 'a1, 'a2, 'a3) F) set" where
  "Fin A1 A2 A3 \<equiv> {x. Fset1 x \<subseteq> A1 \<and> Fset2 x \<subseteq> A2 \<and> Fset3 x \<subseteq> A3}"

abbreviation F'map :: "('a1 \<Rightarrow> 'b1) \<Rightarrow> ('a2 \<Rightarrow> 'b2) \<Rightarrow> ('a3 \<Rightarrow> 'b3) \<Rightarrow> ('p, 'a1, 'a2, 'a3) F' \<Rightarrow> ('p, 'b1, 'b2, 'b3) F'" where
  "F'map f g h \<equiv> Fmap h f g"

abbreviation F'set1 :: "('p, 'a1, 'a2, 'a3) F' \<Rightarrow> 'a1 set" where
  "F'set1 \<equiv> Fset2"

abbreviation F'set2 :: "('p, 'a1, 'a2, 'a3) F' \<Rightarrow> 'a2 set" where
  "F'set2 \<equiv> Fset3"

abbreviation F'set3 :: "('p, 'a1, 'a2, 'a3) F' \<Rightarrow> 'a3 set" where
  "F'set3 \<equiv> Fset1"

abbreviation F'bd where
  "F'bd \<equiv> bd_F"

theorem F'map_id: "F'map id id id = id"
  by (rule F.map_id0)

theorem F'map_comp: "F'map (f1 o g1) (f2 o g2) (f3 o g3) = F'map f1 f2 f3 o F'map g1 g2 g3"
  by (rule F.map_comp0)

theorem F'map_cong: "\<lbrakk>\<And>z. z \<in> F'set1 x \<Longrightarrow> f1 z = g1 z; \<And>z. z \<in> F'set2 x \<Longrightarrow> f2 z = g2 z; \<And>z. z \<in> F'set3 x \<Longrightarrow> f3 z = g3 z\<rbrakk>
  \<Longrightarrow> F'map f1 f2 f3 x = F'map g1 g2 g3 x"
  apply (rule F.map_cong0)
    apply assumption+
  done

theorem F'set1_natural: "F'set1 o F'map f1 f2 f3 = image f1 o F'set1"
  by (rule F.set_map0(2))

theorem F'set2_natural: "F'set2 o F'map f1 f2 f3 = image f2 o F'set2"
  by (rule F.set_map0(3))

theorem F'set3_natural: "F'set3 o F'map f1 f2 f3 = image f3 o F'set3"
  by (rule F.set_map0(1))

theorem F'bd_card_order: "card_order F'bd"
  by (rule F.bd_card_order)

theorem F'bd_cinfinite: "cinfinite F'bd"
  by (rule F.bd_cinfinite)

theorem F'set1_bd: "|F'set1 (x :: ('c, 'a, 'b, 'd) F)| \<le>o (F'bd :: 'c bd_type_F rel)"
  by (rule F.set_bd(2))

theorem F'set2_bd: "|F'set2 (x :: ('c, 'a, 'b, 'd) F)| \<le>o (F'bd :: 'c bd_type_F rel)"
  by (rule F.set_bd(3))

theorem F'set3_bd: "|F'set3 (x :: ('c, 'a, 'b, 'd) F)| \<le>o (F'bd :: 'c bd_type_F rel)"
  by (rule F.set_bd(1))

abbreviation F'in :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('p, 'a1, 'a2, 'a3) F') set" where
  "F'in A1 A2 A3 \<equiv> {x. F'set1 x \<subseteq> A1 \<and> F'set2 x \<subseteq> A2 \<and> F'set3 x \<subseteq> A3}"

lemma F'in_alt: "F'in A1 A2 A3 = Fin A3 A1 A2"
  apply (rule Collect_cong)
  by (tactic \<open>BNF_Tactics.mk_rotate_eq_tac @{context}
  (BNF_Util.rtac @{context} @{thm refl}) @{thm trans} @{thm conj_assoc} @{thm conj_commute} @{thm conj_cong}
  [1, 2, 3] [3, 1, 2] 1\<close>)

definition F'rel where
  "F'rel R1 R2 R3 = (BNF_Def.Grp (F'in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3))) (F'map fst fst fst))^--1 OO
                 (BNF_Def.Grp (F'in (Collect (case_prod R1)) (Collect (case_prod R2)) (Collect (case_prod R3))) (F'map snd snd snd))"


lemmas F'rel_unfold = trans[OF F'rel_def trans[OF OO_Grp_cong[OF F'in_alt] sym[OF F.rel_compp_Grp]]]

bnf F': "('p, 'a1, 'a2, 'a3) F'"
  map: F'map
  sets: F'set1 F'set2 F'set3
  bd: "F'bd :: 'p bd_type_F rel"
  rel: F'rel
              apply -
              apply (rule F'map_id)
             apply (rule F'map_comp)
            apply (erule F'map_cong) apply assumption+
           apply (rule F'set1_natural)
          apply (rule F'set2_natural)
         apply (rule F'set3_natural)
        apply (rule F'bd_card_order)
       apply (rule F'bd_cinfinite)
      apply (rule F'set1_bd)
     apply (rule F'set2_bd)
    apply (rule F'set3_bd)
   apply (unfold F'rel_unfold F.rel_compp[symmetric] eq_OO) [1] apply (rule order_refl)
  apply (rule F'rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  done

(*<*)
end
(*>*)
