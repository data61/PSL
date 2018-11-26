(*  Title:      PSL/MiLkMaId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MiLkMaId: Machine Learning Mathematical Induction for Isabelle/HOL, and
LiFtEr:   Logical Feature Extractor.
*)
theory MiLkMaId_LiFtEr
  imports Main
begin

ML{* (*type synonyms*)
type strings = string list;
type ints    = int    list;
*}

ML_file "Transform_Sig.ML"
ML_file "Transform_Struct.ML"
ML_file "DInduct_Sig.ML"
ML_file "DInduct_Struct.ML"
ML_file "LiFtEr_Sig.ML"
ML_file "LiFtEr_Struct.ML"

end