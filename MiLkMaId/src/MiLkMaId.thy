theory MiLkMaId
  imports Main(*MiLkMaId_Example*)
begin

lemma "True"
  apply induct
  apply induct_tac
  apply induction
  apply induct
  apply induct
  apply auto
  done
(*
ML_file "MiLkMaId_Util.ML"
*)
end