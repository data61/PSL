(*  Title:      PSL/MiLkMaId_LiFtEr/MeLoId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
*)
theory MeLoId_LiFtEr
  imports "../PSL"
  keywords "test_LiFtEr_true" :: diag
   and     "test_LiFtEr_false":: diag
begin

ML{*
@{term "List.nth"}
*}
thm List.nth.simps

ML_file "../src/Utils.ML"
ML_file "../MiLkMaId/src/MiLkMaId_Util.ML"
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

ML{* (*samples*)
local

open LiFtEr_Util LiFtEr;
infix And;

in

val sample_assert =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 2,
       Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)
     And
       Is_Atom (Trm_Occ 2))): assrt;

val sample_induct_args1 = Ind_Mods
 {ons   = [Ind_On (Print "x")],
  arbs  = [Ind_Arb (Print "y")],
  rules = []
  }: ind_mods;

val sample_induct_args2 = Ind_Mods
 {ons   = [Ind_On (Print "x")],
  arbs  = [],
  rules = []
  }: ind_mods;

end;
*}

setup{* Apply_LiFtEr.update_assert 1 sample_assert; *}
ML   {* Apply_LiFtEr.get_assrt @{context} 1;                         *}
setup{* Apply_LiFtEr.update_ind_mod 1 sample_induct_args1;           *}
setup{* Apply_LiFtEr.update_ind_mod 2 sample_induct_args2;           *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} 1;                       *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} 2;                       *}

ML{* Apply_LiFtEr.activate (); *}

lemma "\<not> (\<forall>x. True \<and> x)"
  apply fastforce
  done

schematic_goal "\<not> (True \<and> ?x)"
  apply fastforce
  oops
end