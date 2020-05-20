(*
  File: SepLogic_Base.thy
  Author: Bohua Zhan
*)

theory SepLogic_Base
  imports "Auto2_HOL.Auto2_Main"
begin

text \<open>
  General auto2 setup for separation logic. The automation defined
  here can be instantiated for different variants of separation logic.
\<close>

ML_file "sep_util_base.ML"
ML_file "assn_matcher.ML"
ML_file "sep_steps.ML"

end
