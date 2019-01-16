(*  Title:      PSL/MiLkMaId_LiFtEr/MiLkMaId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MiLkMaId: Machine Learning Mathematical Induction for Isabelle/HOL, and
LiFtEr:   Logical Feature Extractor.
*)
theory MiLkMaId_LiFtEr
  imports Main
begin

ML_file "../src/Utils.ML"

ML{* (*type synonyms*)
type strings = string list;
type ints    = int    list;
*}

ML{*
(* test Term.string_of_vname *)
val should_be_question_Q = @{thm conjI} |> Thm.concl_of |> Term.dest_comb |> snd |> Term.dest_comb
  |> snd |> Term.dest_Var |> fst |> Term.string_of_vname;
@{assert} ("?Q" = should_be_question_Q);
*}

ML_file "../MiLkMaId/src/MiLkMaId_Util.ML"
ML_file "Matrix_Sig.ML"
ML_file "Matrix_Struct.ML"
ML_file "Matrix_Test.ML"
ML_file "LiFtEr_Util_Sig.ML"
ML_file "LiFtEr_Util_Struct.ML"
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
ML{*String.isSubstring "asf" "sf";*}
ML{*String.isSubstring "asf" "sasf";*}

end