(* Author: Dmitriy Traytel *)

theory M2L_Examples
imports M2L_Equivalence_Checking "HOL-Library.Char_ord"
    "HOL-Library.Product_Lexorder"
begin

abbreviation FALSE where "FALSE \<equiv> FExists (FLess 0 0)"
abbreviation TRUE where "TRUE \<equiv> FNot FALSE"
abbreviation All where "All \<phi> \<equiv> FNot (FExists (FNot \<phi>))"
abbreviation AL where "AL \<phi> \<equiv> FNot (FEXISTS (FNot \<phi>))"
abbreviation Imp where "Imp \<phi> \<psi> \<equiv> FOr (FNot \<phi>) \<psi>"
abbreviation Iff where "Iff \<phi> \<psi> \<equiv> FAnd (Imp \<phi> \<psi>) (Imp \<psi> \<phi>)"
abbreviation Ball where "Ball X \<phi> \<equiv> All (Imp (FIn 0 (X+1)) \<phi>)"
abbreviation Bex where "Bex X \<phi> \<equiv> FExists (FAnd (FIn 0 (X+1)) \<phi>)"

abbreviation Eq where "Eq x y \<equiv> FAnd (FNot (FLess x y)) (FNot (FLess y x))"
abbreviation SUBSET where "SUBSET X Y \<equiv> Ball X (FIn 0 (Y+1))"
abbreviation EQ where "EQ X Y \<equiv> FAnd (SUBSET X Y) (SUBSET Y X)"
abbreviation First where "First x \<equiv> FNot (FExists (FLess 0 (x+1)))"
abbreviation Last where "Last x \<equiv> FNot (FExists (FLess (x+1) 0))"
abbreviation Suc where "Suc sucx x \<equiv> FAnd (FLess x sucx) (FNot (FExists (FAnd (FLess (x+1) 0) (FLess 0 (sucx+1)))))"

definition "Thm (type :: 'a :: {enum, linorder} itself) n \<phi> = fast.check_eqv n (FNot \<phi> :: 'a formula) FALSE"
definition "Thm_slow (type :: 'a :: {enum, linorder} itself) n \<phi> = slow.check_eqv n (FNot \<phi> :: 'a formula) FALSE"
definition "Thm_dual (type :: 'a :: {enum, linorder} itself) n \<phi> = dual.check_eqv n (FNot \<phi> :: 'a formula) FALSE"

definition "M2L = (FEXISTS (All (FIn 0 1)) :: Enum.finite_1 formula)"

lemma "Thm TYPE(Enum.finite_1) 0 M2L" by eval
lemma "Thm TYPE(Enum.finite_1) 0 (FNot (All (FExists (FLess 1 0))))" by eval
lemma "Thm (TYPE(bool)) 0 (FNot (FExists (FExists (FAnd (FLess 0 1) (FLess 1 0)))))" by eval
lemma Drinker: "Thm (TYPE(bool)) 1 (FExists (Imp (FIn 0 1) (All (FIn 0 2))))" by eval
lemma "Thm (TYPE(bool)) 1 (Imp (All (FIn 0 1)) (FExists (FIn 0 1)))" by eval

(*
definition "mod_two a b c d = Iff a (Iff b (Iff c d))"
definition "at_least_two a b c d = Iff d (FOr (FAnd a b) (FOr (FAnd b c) (FAnd a c)))"

definition "ADD S A B = FEXISTS (FAnd (All (Imp (First 0) (FNot (FIn 0 1))))
  (All (FAnd (mod_two (FIn 0 (A+2)) (FIn 0 (B+2)) (FIn 0 1) (FIn 0 (S+2)))
       (Imp (FExists (FAnd (Last 0) (FLess 1 0)))
            (at_least_two (FIn 0 (A+2)) (FIn 0 (B+2)) (FIn 0 1) (All (Imp (Suc 0 1) (FIn 0 2))))))))"

definition Comm_Lemma :: "Enum.finite_1 formula" where
  "Comm_Lemma = AL (AL (FEXISTS (FAnd (ADD 0 1 2) (FEXISTS (FAnd (ADD 0 3 2) (EQ 0 1))))))"

lemma "Thm TYPE(bool) 0 (AL (AL (FEXISTS (ADD 0 1 2))))"
  by eval

lemma "Thm TYPE(Enum.finite_1) 0 Comm_Lemma"
  by eval
*)

abbreviation Globally ("\<box>_" [40] 40) where "Globally P == %n. All (Imp (FNot (FLess (n+1) 0)) (P 0))"
abbreviation Future ("\<diamond>_" [40] 40) where "Future P == %n. FExists (FAnd (FNot (FLess (n+1) 0)) (P 0))"
abbreviation IMP (infixr "\<rightarrow>" 50) where "IMP P1 P2 == %n. Imp (P1 n) (P2 n)"

abbreviation "FOR xs n \<equiv> rexp_of_list FOr FALSE (map (\<lambda>x. FQ x n) xs)"

abbreviation \<Phi>0 :: "bool formula" where "\<Phi>0 \<equiv>
  (All (((\<box>(FOR [(True)])) \<rightarrow> (\<box>(FOR [(True)]))) 0))"

abbreviation \<Phi>1 :: "(bool \<times> bool) formula" where "\<Phi>1 \<equiv>
  (All (((\<box>(FOR [(True, True), (True, False)] \<rightarrow>
            FOR [(True, True), (False, True)])) \<rightarrow>
         (\<box>(FOR [(True, True), (True, False)])) \<rightarrow>
         (\<box>(FOR [(True, True), (False, True)]))) 0))"

abbreviation \<Phi>2 :: "(bool \<times> bool \<times> bool) formula" where "\<Phi>2 \<equiv> 
  (All (((\<box>(FOR [(True, True, True), (True, True, False), (True, False, True), (True, False, False)] \<rightarrow>
            FOR [(True, True, True), (True, True, False), (False, True, True), (False, True, False)] \<rightarrow>
            FOR [(True, True, True), (True, False, True), (False, True, True), (False, False, True)])) \<rightarrow>
        (\<box>(FOR [(True, True, True), (True, True, False), (True, False, True), (True, False, False)])) \<rightarrow>
        (\<box>(FOR [(True, True, True), (True, True, False), (False, True, True), (False, True, False)])) \<rightarrow>
        (\<box>(FOR [(True, True, True), (True, True, False), (False, True, True), (False, True, False)]))) 0))"

definition \<Psi> :: "nat \<Rightarrow> Enum.finite_1 formula" where
  "\<Psi> n = All (((\<box>(foldr (\<lambda>i \<phi>. (\<lambda>m. FIn m (2 + i)) \<rightarrow> \<phi>) [0..<n] (\<lambda>m. FIn m (n + 2)))) \<rightarrow>
     foldr (\<lambda>i \<phi>. (\<box>(\<lambda>m. FIn m (2 + i))) \<rightarrow> \<phi>) [0..<n] (\<box>(\<lambda>m. FIn m (n + 2)))) 0)"

definition "Thm1 n = Thm (TYPE(Enum.finite_1)) (n + 1) (\<Psi> n)"
definition "Thm1_slow n = Thm_slow (TYPE(Enum.finite_1)) (n + 1) (\<Psi> n)"
definition "Thm1_dual n = Thm_dual (TYPE(Enum.finite_1)) (n + 1) (\<Psi> n)"

lemma "Thm1 0" by eval
lemma "Thm1 1" by eval
lemma "Thm1 2" by eval

lemma "Thm (TYPE(bool)) 0 \<Phi>0" by eval
lemma "Thm (TYPE(bool * bool)) 0 \<Phi>1" by eval
lemma "Thm (TYPE(bool * bool * bool)) 0 \<Phi>2" by eval

(*
export_code Thm1 Nat in SML module_name M2L_Thm1 file "M2L_Thm1.ML"
export_code Thm1_slow Nat in SML module_name M2L_Thm1_slow file "M2L_Thm1_slow.ML"
export_code Thm1_dual Nat in SML module_name M2L_Thm1_dual file "M2L_Thm1_dual.ML"

ML_file "M2L_Thm1.ML"
ML_file "M2L_Thm1_slow.ML"
ML_file "M2L_Thm1_dual.ML"

ML {* PolyML.timing true; open M2L_Thm1; thm1 (Nat 0); thm1 (Nat 1); thm1 (Nat 2); thm1 (Nat 3); *}
ML {* PolyML.timing true; open M2L_Thm1_dual; thm1_dual (Nat 0); thm1_dual (Nat 1); thm1_dual (Nat 2); thm1_dual (Nat 3); *}
ML {* PolyML.timing true; open M2L_Thm1_slow; thm1_slow (Nat 0); thm1_slow (Nat 1); thm1_slow (Nat 2); *}
*)
end
