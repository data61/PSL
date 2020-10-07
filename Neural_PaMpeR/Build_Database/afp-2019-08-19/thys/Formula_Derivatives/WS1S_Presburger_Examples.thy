section \<open>Examples for the WS1S/Presburger Mixture\<close>

(*<*)
theory WS1S_Presburger_Examples
imports
  Formula_Derivatives.WS1S_Presburger_Equivalence
begin
(*>*)

lemma "check_eqv (Abs_idx (0, 0)) 0 (FEx SO (FBase (Eq_Presb None 0 42))) (FEx () (FBase (Eq [1] 42 0)))"
  by check_equiv

lemma "check_eqv (Abs_idx (0, 1)) 1 (FBase (Eq_Presb None 0 42)) (FBase (Eq [1] 42 0))"
  by check_equiv

lemma "check_eqv (Abs_idx (0, 2)) 2 (FBase (Suc_SO False False 1 0)) (FBase (Eq [2, -1] 0 0))"
  by check_equiv

lemma "check_eqv (Abs_idx (0, 1)) 1 (FBase (Empty 0)) (FBase (Eq [1] 0 0))"
  by check_equiv

lemma "check_eqv (Abs_idx (0, 1)) 1 (FBase (Empty 0)) (FBase (Eq [-1] 0 0))"
  by check_equiv

lemma "check_eqv (Abs_idx (0, 0)) 0
  (FNot (FEx SO (FAll FO (FBase (In False 0 0)))))
  (FAll () (FEx () (FEx () (FBase (Eq [3, 5, -1] 8 0)))))"
  by check_equiv

(*<*)
end
(*>*)
