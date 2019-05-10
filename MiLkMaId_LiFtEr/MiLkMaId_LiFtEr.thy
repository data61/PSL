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
ML_file "Apply_MeLoId.ML"

ML{* (*samples*)
val sample_induct_args1 = TL.Ind_Mods
 {ons   = [TL.Ind_On (TL.Print "x")],
  arbs  = [TL.Ind_Arb (TL.Print "y")],
  rules = []
  }: TL.ind_mods;

val sample_induct_args2 = TL.Ind_Mods
 {ons   = [TL.Ind_On (TL.Print "x")],
  arbs  = [],
  rules = []
  }: TL.ind_mods;

local
structure L = LiFtEr;
in
infix And;
val op And = L.And

 val sample_assert =
  L.All_Ind (L.Sub_Trm 1,
    L.Some_Sub_Trm_Occ (L.Sub_Trm_Occ 2,
        L.Trm_Occ_Is_Of_Trm (L.Sub_Trm_Occ 2, L.Sub_Trm 1)
      And
        L.Is_Atom (L.Sub_Trm_Occ 2))): L.assrt;
end
*}

setup{* update_assert 1 sample_assert; *}
ML   {* get_assrt @{context} 1;    *}
setup{* update_ind_mod 1 sample_induct_args1; *}
setup{* update_ind_mod 2 sample_induct_args2; *}
ML   {* get_ind_mod @{context} 1;    *}
ML   {* get_ind_mod @{context} 2;    *}

lemma "True"
  test_LiFtEr_true 1 1
  oops

end