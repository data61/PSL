(*  Title:      PSL/LiFtEr/MeLoId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
*)
theory LiFtEr
  imports "SeLFiE.SeLFiE" Main
  keywords "assert_LiFtEr_true" :: diag
   and     "assert_LiFtEr_false":: diag
   and     "assert_LiFtEr"      :: diag
   and     "test_all_LiFtErs"   :: diag
begin

ML_file "Matrix_Sig.ML"
ML_file "Matrix_Struct.ML"
ML_file "Matrix_Test.ML"
ML_file "LiFtEr_Util_Sig.ML"
ML_file "LiFtEr_Util_Struct.ML"
ML_file "Pattern_Sig.ML"
ML_file "Pattern_Struct.ML"
ML_file "Pattern_Test.ML"
ML_file "Unique_Node_Sig.ML"
ML_file "Unique_Node_Struct.ML"
ML_file "Unique_Node_Test.ML"
ML_file "Term_Table_Sig.ML"
ML_file "Term_Table_Struct.ML"
ML_file "Term_Table_Test.ML"
ML_file "DInduct_Sig.ML"
ML_file "DInduct_Struct.ML"
ML_file "LiFtEr_Sig.ML"
ML_file "LiFtEr_Struct.ML"
ML_file "Apply_LiFtEr_Sig.ML"
ML_file "Apply_LiFtEr_Struct.ML"
ML_file "LiFtEr_Assertion_Struct.ML"

ML\<open> Apply_LiFtEr.activate ();  \<close>
ML\<open> Apply_LiFtEr.activate2 (); \<close>
ML\<open> Apply_LiFtEr.activate3 (); \<close>

end