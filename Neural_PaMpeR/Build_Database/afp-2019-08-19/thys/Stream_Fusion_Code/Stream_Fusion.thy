(* Title: Stream_Fusion.thy
 Authors: Alexandra Maximova, ETH Zurich
          Andreas Lochbihler, ETH Zurich
*)

section \<open>Stream fusion implementation\<close>

theory Stream_Fusion
imports
  Main
begin

ML_file \<open>stream_fusion.ML\<close>

simproc_setup stream_fusion ("f x") = \<open>K Stream_Fusion.fusion_simproc\<close>
declare [[simproc del: stream_fusion]]

text \<open>Install stream fusion as a simproc in the preprocessor for code equations\<close>
setup \<open>Code_Preproc.map_pre (fn ss => ss addsimprocs [@{simproc "stream_fusion"}])\<close>

end
