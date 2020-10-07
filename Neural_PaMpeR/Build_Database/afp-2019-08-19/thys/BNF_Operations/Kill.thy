(*  Title:       Kill
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Removing Live Variables\<close>

(*<*)
theory Kill
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

unbundle cardinal_syntax

declare [[bnf_internals]]
bnf_axiomatization (dead 'p, Fset1: 'a1, Fset2: 'a2, Fset3: 'a3) F for map: Fmap rel: Frel

abbreviation F1map :: "('a2 \<Rightarrow> 'b2) \<Rightarrow> ('a3 \<Rightarrow> 'b3) \<Rightarrow> ('p, 'a1, 'a2, 'a3) F \<Rightarrow> ('p, 'a1, 'b2, 'b3) F" where
  "F1map \<equiv> Fmap id"
abbreviation F2map :: "('a3 \<Rightarrow> 'b3) \<Rightarrow> ('p, 'a1, 'a2, 'a3) F \<Rightarrow> ('p, 'a1, 'a2, 'b3) F" where
  "F2map \<equiv> Fmap id id"

abbreviation "F1set1 \<equiv> Fset2"
abbreviation "F1set2 \<equiv> Fset3"
abbreviation "F2set \<equiv> Fset3"


theorem F1map_id: "F1map id id = id"
  by (rule F.map_id0)

theorem F2map_id: "F2map id = id"
  by (rule F.map_id0)

theorem F1map_comp: "F1map (f1 o g1) (f2 o g2) = F1map f1 f2 o F1map g1 g2"
  by (unfold F.map_comp0[symmetric] o_id) (rule refl)

theorem F2map_comp: "F2map (f o g) = F2map f o F2map g"
  by (unfold F.map_comp0[symmetric] o_id) (rule refl)

theorem F1map_cong: "\<lbrakk>\<And>z. z \<in> F1set1 x \<Longrightarrow> f1 z = g1 z; \<And>z. z \<in> F1set2 x \<Longrightarrow> f2 z = g2 z\<rbrakk>
  \<Longrightarrow> F1map f1 f2 x = F1map g1 g2 x"
  apply (rule F.map_cong0)
    apply (rule refl)
   apply assumption
  apply assumption
  done

theorem F2map_cong: "\<lbrakk>\<And>z. z \<in> F2set x \<Longrightarrow> f z = g z\<rbrakk> \<Longrightarrow> F2map f x = F2map g x"
  apply (rule F.map_cong0)
    apply (rule refl)
   apply (rule refl)
  apply assumption
  done

theorem F1set1_natural: "F1set1 o F1map f1 f2 = image f1 o F1set1"
  by (rule F.set_map0(2))

theorem F1set2_natural: "F1set2 o F1map f1 f2 = image f2 o F1set2"
  by (rule F.set_map0(3))

theorem F2set_natural: "F2set o F2map f = image f o F2set"
  by (rule F.set_map0(3))

abbreviation Fin :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('p, 'a1, 'a2, 'a3) F) set" where
  "Fin A1 A2 A3 \<equiv> {x. Fset1 x \<subseteq> A1 \<and> Fset2 x \<subseteq> A2 \<and> Fset3 x \<subseteq> A3}"

abbreviation F1in :: "'a2 set \<Rightarrow> 'a3 set \<Rightarrow> (('p, 'a1, 'a2, 'a3) F) set" where
  "F1in A1 A2 \<equiv> {x. F1set1 x \<subseteq> A1 \<and> F1set2 x \<subseteq> A2}"

lemma F1in_alt: "F1in A2 A3 = Fin UNIV A2 A3"
  by (tactic \<open>BNF_Comp_Tactics.kill_in_alt_tac @{context}\<close>)

abbreviation F2in :: "'a3 set \<Rightarrow> (('p, 'a1, 'a2, 'a3) F) set" where
  "F2in A \<equiv> {x. F2set x \<subseteq> A}"

lemma F2in_alt: "F2in A3 = Fin UNIV UNIV A3"
  by (tactic \<open>BNF_Comp_Tactics.kill_in_alt_tac @{context}\<close>)

lemma Frel_cong: "\<lbrakk>R1 = S1; R2 = S2; R3 = S3\<rbrakk> \<Longrightarrow> Frel R1 R2 R3 = Frel S1 S2 S3"
  by hypsubst (rule refl)

definition F1rel where
  "F1rel R1 R2 = (BNF_Def.Grp (F1in (Collect (case_prod R1)) (Collect (case_prod R2))) (F1map fst fst))^--1 OO
                 (BNF_Def.Grp (F1in (Collect (case_prod R1)) (Collect (case_prod R2))) (F1map snd snd))"

lemmas F1rel_unfold = trans[OF F1rel_def trans[OF OO_Grp_cong[OF F1in_alt]
      trans[OF arg_cong2[of _ _ _ _ relcompp, OF trans[OF arg_cong[of _ _ conversep, OF sym[OF F.rel_Grp]] F.rel_conversep[symmetric]] sym[OF F.rel_Grp]]
        trans[OF F.rel_compp[symmetric] Frel_cong[OF trans[OF Grp_UNIV_id[OF refl] eq_alt[symmetric]] Grp_fst_snd Grp_fst_snd]]]]]

definition F2rel where
  "F2rel R1 = (BNF_Def.Grp (F2in (Collect (case_prod R1))) (F2map fst))^--1 OO
              (BNF_Def.Grp (F2in (Collect (case_prod R1))) (F2map snd))"

lemmas F2rel_unfold = trans[OF F2rel_def trans[OF OO_Grp_cong[OF F2in_alt]
      trans[OF arg_cong2[of _ _ _ _ relcompp, OF trans[OF arg_cong[of _ _ conversep, OF sym[OF F.rel_Grp]] F.rel_conversep[symmetric]] sym[OF F.rel_Grp]]
        trans[OF F.rel_compp[symmetric] Frel_cong[OF trans[OF Grp_UNIV_id[OF refl] eq_alt[symmetric]] trans[OF Grp_UNIV_id[OF refl] eq_alt[symmetric]] Grp_fst_snd]]]]]

bnf F1: "('p, 'a1, 'a2, 'a3) F"
  map: F1map
  sets: F1set1 F1set2
  bd: "bd_F :: ('p bd_type_F) rel"
  rel: F1rel
            apply -
            apply (rule F1map_id)
           apply (rule F1map_comp)
          apply (erule F1map_cong) apply assumption
         apply (rule F1set1_natural)
        apply (rule F1set2_natural)
       apply (rule F.bd_card_order)
      apply (rule F.bd_cinfinite)
     apply (rule F.set_bd(2))
    apply (rule F.set_bd(3))
   apply (unfold F1rel_unfold F.rel_compp[symmetric] eq_OO) [1] apply (rule order_refl)
  apply (rule F1rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  done

bnf F2: "('p, 'a1, 'a2, 'a3) F"
  map: F2map
  sets: F2set
  bd: "bd_F :: ('p bd_type_F) rel"
  rel: F2rel
          apply -
          apply (rule F2map_id)
         apply (rule F2map_comp)
        apply (erule F2map_cong)
       apply (rule F2set_natural)
      apply (rule F.bd_card_order)
     apply (rule F.bd_cinfinite)
    apply (rule F.set_bd(3))
   apply (unfold F2rel_unfold F.rel_compp[symmetric] eq_OO) [1] apply (rule order_refl)
  apply (rule F2rel_def[unfolded OO_Grp_alt mem_Collect_eq])
  done

(*<*)
end
(*>*)
