(*  Title:      MeLoId/src/Build_Database.thy
    Author:     Yutaka Nagashima, CTU, CIIRC, University of Innsbruck
*)
theory Build_Database
  imports "../../../PSL/src/Try_Hard"
(*
  keywords "apply2" :: prf_script
   and "proof2" :: prf_block
   and     "by2" (*"proof2"*) :: "qed"
*)
begin

ML{*
infix 1 >>= <$>;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;
*}

ML_file "../../../PSL/src/Utils.ML"
ML_file "../MeLoId_Util.ML"
ML_file "../Smart_Induct.ML"
ML_file "FE_Interface.ML"

ML{* FE_Interface.FE_activate (); *}

end