theory Build_Database
  imports "../../../src/Try_Hard"
  keywords "apply2" :: prf_script
(*   and     "by2" (*"proof2"*) :: "qed"*)
begin

ML{*
infix 1 >>= <$>;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;
*}

ML_file "../../../src/Utils.ML"
ML_file "../MiLkMaId_Assertion.ML"
ML_file "../Smart_Induct.ML"
ML_file "FE_Interface.ML"

ML{* FE_Interface.FE_activate (); *}

end