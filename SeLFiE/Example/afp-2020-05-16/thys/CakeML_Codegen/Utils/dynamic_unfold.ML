signature DYNAMIC_UNFOLD = sig
  val enabled: bool Config.T
  val simproc: morphism -> Proof.context -> cterm -> thm option
end

structure Dynamic_Unfold : DYNAMIC_UNFOLD = struct

val enabled = Attrib.setup_config_bool @{binding "dynamic_unfold"} (K false)

open Dict_Construction_Util

fun simproc _ ctxt ct =
  if Config.get ctxt enabled then
    let
      val ctxt = Config.put enabled false ctxt
      val thy = Proof_Context.theory_of ctxt
      val unfold_thms =
        all_consts (Thm.term_of ct)
        |> filter (not o can dest_funT o snd)
        |> map (snd o Code.equations_of_cert thy o Code.get_cert ctxt [] o fst)
        |> cat_options
        |> flat
        |> map (fst o snd)
        |> cat_options
    in
      if null unfold_thms then
        NONE
      else
        (* in principle this should *always* change something, but we better wrap it in
           changed_conv to at least throw an error instead of loop *)
        SOME (changed_conv (Raw_Simplifier.rewrite ctxt false unfold_thms) ct)
    end
  else
    NONE

end