section \<open>Examples for Nameful WS1S Formulas\<close>

(*<*)
theory WS1S_Nameful_Examples
imports Formula_Derivatives.WS1S_Nameful Show.Show_Instances
begin
(*>*)

lift_definition x :: fo is "''x''" by simp
lift_definition y :: fo is "''y''" by simp
lift_definition z :: fo is "''z''" by simp
lift_definition X :: so is "''X''" by simp
lift_definition Y :: so is "''Y''" by simp
lift_definition Z :: so is "''Z''" by simp
lift_definition Xi :: "nat \<Rightarrow> so" is "\<lambda>i. ''X'' @ show i" by simp

abbreviation Imp where "Imp \<phi> \<psi> \<equiv> Or (Not \<phi>) \<psi>"
(*true in M2L, false in WS1S*)
definition "M2L = Ex2 X (All1 x (In x X))"
(*false in M2L, true in WS1S*)
definition "\<Phi> = All1 x (Ex1 y (Lt x y))"

abbreviation Globally ("\<box>_" [40] 40) where
  "Globally P t ==  All1 z (Imp (Not (Lt t z)) (P z))"
abbreviation Future ("\<diamond>_" [40] 40) where
  "Future P t == Ex1 z (And (Not (Lt t z)) (P z))"
abbreviation IMP (infixr "\<rightarrow>" 50) where "IMP P1 P2 t == Imp (P1 t) (P2 t)"

definition \<Psi> :: "nat \<Rightarrow> ws1s" where
  "\<Psi> n = All1 x
     (((\<box>(foldr (\<lambda>i \<phi>. (\<lambda>m. In m (Xi i)) \<rightarrow> \<phi>) [0..<n] (\<lambda>m. (In m (Xi n))))) \<rightarrow>
     foldr (\<lambda>i \<phi>. (\<box>(\<lambda>m. (In m (Xi i)))) \<rightarrow> \<phi>) [0..<n]
       (\<box>(\<lambda>m. (In m (Xi n))))) x)"

method_setup check_equiv = \<open>
  let
    fun tac ctxt =
      let
        val conv = @{computation_check terms: Trueprop
          "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "plus :: nat \<Rightarrow> _" "minus :: nat \<Rightarrow> _"
          "times :: nat \<Rightarrow> _" "divide :: nat \<Rightarrow> _" "modulo :: nat \<Rightarrow> _"
          "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          Thm x y z X Y Z Xi \<Psi> \<Phi> M2L eqv datatypes: formula "int list" integer idx
         "nat \<times> nat" "nat option" "bool option" ws1s} ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o tac)
  end
\<close>

lemma "Thm (Not M2L)"
  by check_equiv

lemma "Thm \<Phi>"
  by check_equiv

lemma "eqv (And (Eq_Const x 10) (Eq_Const x 10000)) F"
  by check_equiv

lemma "Thm (\<Psi> 0)"
  by check_equiv

lemma "Thm (\<Psi> 1)"
  by check_equiv

lemma "Thm (\<Psi> 2)"
  by check_equiv

lemma "Thm (\<Psi> 3)"
  by check_equiv

lemma "Thm (\<Psi> 4)"
  by check_equiv

lemma "Thm (\<Psi> 5)"
  by check_equiv

lemma "Thm (\<Psi> 10)"
  by check_equiv

lemma "Thm (\<Psi> 15)"
  by check_equiv

(*<*)
end
(*>*)
