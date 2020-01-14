(*  Title:      PSL/LiFtEr/MeLoId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
*)
theory LiFtEr
  imports "../PSL"
  keywords "assert_LiFtEr_true" :: diag
   and     "assert_LiFtEr_false":: diag
   and     "assert_LiFtEr"      :: diag
   and     "test_all_LiFtErs"   :: diag
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

ML\<open> Apply_LiFtEr.activate ();  \<close>
ML\<open> Apply_LiFtEr.activate2 (); \<close>
ML\<open> Apply_LiFtEr.activate3 (); \<close>

ML\<open>
Symbol.is_printable "\<pi>";
Symbol.is_printable ",";
Symbol.is_printable "(";
Symbol.is_printable "\"";

fun is_non_quatation_string str = not (str = "\"");

type d = String.string;
local
  open Parser_Combinator;
in

infix plus;

val non_quote_symbol = sat (fn x => not (x = "\""))
  : symbols -> (string * symbols) Seq.seq;

fun non_quotation_word' _ =
  let
    val neWord = non_quote_symbol >>= (fn x =>
                 non_quotation_word' () >>= (fn xs =>
                 result (x ^ xs))):  symbols -> (string * symbols) Seq.seq;
  in
    neWord plus result ""
 end: string parser;

val non_quotation_word = non_quotation_word' () plus result "": string Parser_Combinator.parser;

val parse_quotation =
bracket
 (string "\"" |> token)
 (non_quotation_word |> token)
 (string "\"" |> token):  string Parser_Combinator.parser;
 
end;

val aa = exists (fn _ => true) []
\<close>

end