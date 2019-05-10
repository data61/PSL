(*  Title:      PSL/MiLkMaId_LiFtEr/MiLkMaId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MiLkMaId: Machine Learning Mathematical Induction for Isabelle/HOL, and
LiFtEr:   Logical Feature Extractor.
*)
theory MiLkMaId_LiFtEr
  imports "../PSL"
  keywords "test_LiFtEr_true" :: diag
   and     "test_LiFtEr_false":: diag
begin

ML_file "../src/Utils.ML"

ML{* (*type synonyms*)
type strings = string list;
type ints    = int    list;
*}

ML_file "../MiLkMaId/src/MiLkMaId_Util.ML"
ML_file "Matrix_Sig.ML"
ML_file "Matrix_Struct.ML"
ML_file "Matrix_Test.ML"
ML_file "LiFtEr_Util_Sig.ML"
ML_file "LiFtEr_Util_Struct.ML"
ML_file "Pattern_Sig.ML"
ML_file "Pattern_Struct.ML"
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

ML{* (*samples*)
local

structure LU = LiFtEr_Util;
structure L = LiFtEr;

in

val sample_induct_args1 = LU.Ind_Mods
 {ons   = [LU.Ind_On (LU.Print "x")],
  arbs  = [LU.Ind_Arb (LU.Print "y")],
  rules = []
  }: LU.ind_mods;

val sample_induct_args2 = LU.Ind_Mods
 {ons   = [LU.Ind_On (LU.Print "x")],
  arbs  = [],
  rules = []
  }: LU.ind_mods;

infix And;
val op And = L.And

 val sample_assert =
  L.All_Ind (L.Sub_Trm 1,
    L.Some_Sub_Trm_Occ (L.Sub_Trm_Occ 2,
        L.Trm_Occ_Is_Of_Trm (L.Sub_Trm_Occ 2, L.Sub_Trm 1)
      And
        L.Is_Atom (L.Sub_Trm_Occ 2))): L.assrt;
end;
*}

setup{* Apply_LiFtEr.update_assert 1 sample_assert;        *}
ML   {* Apply_LiFtEr.get_assrt @{context} 1;               *}
setup{* Apply_LiFtEr.update_ind_mod 1 sample_induct_args1; *}
setup{* Apply_LiFtEr.update_ind_mod 2 sample_induct_args2; *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} 1;             *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} 2;             *}

ML{* Apply_LiFtEr.activate (); *}

lemma "True"
  test_LiFtEr_true 1 1
  oops

end