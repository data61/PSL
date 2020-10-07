
section \<open>Examples for Presburger Arithmetics\<close>

(*<*)
theory Presburger_Examples
imports Formula_Derivatives.Presburger_Formula
begin
(*>*)

definition "phi = FAll () (FEx () (FEx () (FBase (Eq [3, 5, -1] 8 0))))"
definition "lemma (_ :: unit) = check_eqv 0 phi (FBool True)"

lemma "check_eqv 0 (FAll () (FEx () (FEx () (FBase (Eq [3, 5, -1] 7 0))))) (FBool False)"
  by check_equiv

lemma "check_eqv 0 (FAll () (FEx () (FEx () (FBase (Eq [3, 5, -1] 8 0))))) (FBool True)"
  by check_equiv

lemma "check_eqv 0 (FAll () (FEx () (FEx () (FBase (Eq [4, 5, -1] 8 0))))) (FBool False)"
  by check_equiv

(*
value "check_eqv 0 (FEx () (FEx () (FEx () (FEx () (FEx () (FEx ()
  (fold FAnd [               
    FBase (Eq [-4, 5, 0, 0, 0, 0] 1 0),
    FBase (Eq [0, -4, 5, 0, 0, 0] 1 0),
    FBase (Eq [0, 0, -4, 5, 0, 0] 1 0),
    FBase (Eq [0, 0, 0, -4, 5, 0] 1 0),
    FBase (Eq [0, 0, 0, 0, -4, 5] 1 0)] (FBool True)))))))) (FBool True)"
*)

(*<*)
end
(*>*)
