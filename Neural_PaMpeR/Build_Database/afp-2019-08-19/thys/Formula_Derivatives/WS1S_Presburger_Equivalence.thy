section \<open>Comparing WS1S Formulas with Presburger Formulas\<close>

(*<*)
theory WS1S_Presburger_Equivalence
imports Presburger_Formula WS1S_Formula
begin
(*>*)

lift_definition letter_eq :: "idx \<Rightarrow> nat \<Rightarrow> bool list \<times> bool list \<Rightarrow> bool list \<Rightarrow> bool" is
  "\<lambda>(m1,m2) n (bs1, bs2) bs. m1 = 0 \<and> m2 = n \<and> bs1 = [] \<and> bs2 = bs" .

lemma letter_eq[dest]:
  "letter_eq idx n a b \<Longrightarrow> (a \<in> set (WS1S_Prelim.\<sigma> idx)) = (b \<in> set (Presburger_Formula.\<sigma> n))"
  by transfer (force simp: Presburger_Formula.\<sigma>_def set_n_lists image_iff)

global_interpretation WS1S_Presb: DAs
  "WS1S_Prelim.\<sigma> idx"
  "(\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)"
  "(\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi>))"
  "(WS1S.final idx)"
  "(\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)"
  "\<lambda>\<phi>. Formula.lang WS1S_Prelim.nvars
     WS1S_Prelim.Extend WS1S_Prelim.CONS WS1S_Prelim.Length WS1S_Prelim.size_atom
     WS1S_Formula.satisfies0 idx \<phi>"
  "(\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)"
  "\<lambda>\<phi>. Formula.language WS1S_Prelim.assigns
     WS1S_Prelim.nvars WS1S_Prelim.Extend WS1S_Prelim.CONS
     WS1S_Prelim.Length WS1S_Prelim.size_atom restrict WS1S_Formula.FV0
     WS1S_Formula.satisfies0 idx \<phi>"
  "(Presburger_Formula.\<sigma> n)"
  "(\<lambda>\<phi>. Presburger_Formula.norm (Presburger_Formula.RESTRICT \<phi>))"
  "(\<lambda>a \<phi>. Presburger_Formula.norm (Presburger_Formula.deriv Presburger_Formula.lderiv0 a \<phi>))"
  "(Presburger_Formula.final n)"
  "(\<lambda>\<phi>. presb_wf n \<phi> \<and> presb_lformula \<phi>)"
  "(\<lambda>\<phi>. Formula.lang Presburger_Formula.nvars
            Presburger_Formula.Extend Presburger_Formula.CONS Presburger_Formula.Length
            Presburger_Formula.size_atom (\<Turnstile>0) n \<phi>)"
  "(\<lambda>\<phi>. presb_wf n \<phi> \<and> presb_lformula \<phi>)"
  "(\<lambda>\<phi>. Formula.language Presburger_Formula.assigns
            Presburger_Formula.nvars Presburger_Formula.Extend Presburger_Formula.CONS
            Presburger_Formula.Length Presburger_Formula.size_atom (\<lambda>_ _. True)
            Presburger_Formula.FV0 (\<Turnstile>0)
            n \<phi>)"
  "letter_eq idx n"
  defines check_eqv = "\<lambda>idx n. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)
    (Presburger_Formula.\<sigma> n) (\<lambda>\<phi>. Presburger_Formula.norm (Presburger_Formula.RESTRICT \<phi>))
    (\<lambda>a \<phi>. Presburger_Formula.norm (Presburger_Formula.deriv Presburger_Formula.lderiv0 a \<phi>))
    (Presburger_Formula.final n) (\<lambda>\<phi>. presb_wf n \<phi> \<and> presb_lformula \<phi>) (letter_eq idx n)"
  by unfold_locales auto

(*Workaround for code generation*)
lemma check_eqv_code[code]: "check_eqv idx n r s \<longleftrightarrow>
  ((ws1s_wf idx r \<and> ws1s_lformula r) \<and> (presb_wf n s \<and> presb_lformula s) \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = Presburger_Formula.final n q)
  (\<lambda>(p, q).
    map (\<lambda>(a, b). (norm (deriv lderiv0 a p),
      Presburger_Formula.norm (Presburger_Formula.deriv Presburger_Formula.lderiv0 b q)))
     [(x, y)\<leftarrow>List.product (\<sigma> idx) (Presburger_Formula.\<sigma> n). letter_eq idx n x y])
    (norm (RESTRICT r), Presburger_Formula.norm (Presburger_Formula.RESTRICT s)) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def WS1S_Presb.check_eqv_def ..

method_setup check_equiv = \<open>
  let
    fun tac ctxt =
      let
        val conv = @{computation_check terms: Trueprop
          "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "plus :: nat \<Rightarrow> _" "minus :: nat \<Rightarrow> _"
          "times :: nat \<Rightarrow> _" "divide :: nat \<Rightarrow> _" "modulo :: nat \<Rightarrow> _"
          "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          check_eqv datatypes: idx "(presb, unit) aformula" "((nat, nat) atomic, WS1S_Prelim.order) aformula"
          "nat \<times> nat" "nat option" "bool option" "int list" integer} ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o tac)
  end
\<close>

(*<*)
end
(*>*)
