(*  Title:      PSL/LiFtEr/MeLoId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
*)
theory LiFtEr
  imports "../PSL"
  keywords "assert_LiFtEr_true" :: diag
   and     "assert_LiFtEr_false":: diag
begin

ML_file "../src/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "src/Matrix_Sig.ML"
ML_file "src/Matrix_Struct.ML"
ML_file "src/Matrix_Test.ML"
ML_file "src/LiFtEr_Util_Sig.ML"
ML_file "src/LiFtEr_Util_Struct.ML"
ML_file "src/Pattern_Sig.ML"
ML_file "src/Pattern_Struct.ML"
ML_file "src/Pattern_Test.ML"
ML_file "src/Unique_Node_Sig.ML"
ML_file "src/Unique_Node_Struct.ML"
ML_file "src/Unique_Node_Test.ML"
ML_file "src/Term_Table_Sig.ML"
ML_file "src/Term_Table_Struct.ML"
ML_file "src/Term_Table_Test.ML"
ML_file "src/DInduct_Sig.ML"
ML_file "src/DInduct_Struct.ML"
ML_file "src/LiFtEr_Sig.ML"
ML_file "src/LiFtEr_Struct.ML"
ML_file "src/Apply_LiFtEr_Sig.ML"
ML_file "src/Apply_LiFtEr_Struct.ML"
ML_file "src/LiFtEr_Assertion_Struct.ML"

ML\<open> Apply_LiFtEr.activate (); \<close>

end