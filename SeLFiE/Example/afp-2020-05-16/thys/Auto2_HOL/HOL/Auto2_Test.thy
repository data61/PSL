(*
  File: Auto2_Test.thy
  Author: Bohua Zhan

  Unit tests for auto2.
*)

theory Auto2_Test
  imports Auto2_Main
begin

ML_file \<open>util_test.ML\<close>
ML_file \<open>rewrite_test.ML\<close>
ML_file \<open>matcher_test.ML\<close>
ML_file \<open>normalize_test.ML\<close>
ML_file \<open>logic_steps_test.ML\<close>

ML_file \<open>acdata_test.ML\<close>

end
