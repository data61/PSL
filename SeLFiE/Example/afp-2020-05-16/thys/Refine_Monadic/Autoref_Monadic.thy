section "Autoref for the Refinement Monad"
theory Autoref_Monadic
imports Refine_Transfer
begin

text \<open>Default setup of the autoref-tool for the monadic framework.\<close>

lemma autoref_monadicI1:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "RETURN c \<le> b"
  shows "(RETURN c, a)\<in>\<langle>R\<rangle>nres_rel" "RETURN c \<le>\<Down>R a"
  using assms
  unfolding nres_rel_def
  by simp_all

lemma autoref_monadicI2:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "nres_of c \<le> b"
  shows "(nres_of c, a)\<in>\<langle>R\<rangle>nres_rel" "nres_of c \<le> \<Down>R a"
  using assms
  unfolding nres_rel_def
  by simp_all

lemmas autoref_monadicI = autoref_monadicI1 autoref_monadicI2

ML \<open>
  structure Autoref_Monadic = struct

    val cfg_plain = Attrib.setup_config_bool @{binding autoref_plain} (K false)

    fun autoref_monadic_tac ctxt = let
      open Autoref_Tacticals
      val ctxt = Autoref_Phases.init_data ctxt
      val plain = Config.get ctxt cfg_plain
      val trans_thms = if plain then [] else @{thms the_resI}
  
    in
      resolve_tac ctxt @{thms autoref_monadicI}
      THEN' 
      IF_SOLVED (Autoref_Phases.all_phases_tac ctxt)
        (RefineG_Transfer.post_transfer_tac trans_thms ctxt)
        (K all_tac) (* Autoref failed *)

    end
  end
\<close>

method_setup autoref_monadic = \<open>let
    open Refine_Util Autoref_Monadic
    val autoref_flags = 
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "plain" Autoref_Monadic.cfg_plain

  in
    parse_paren_lists autoref_flags 
    >>
    ( fn _ => fn ctxt => SIMPLE_METHOD' (
      let 
        val ctxt = Config.put Autoref_Phases.cfg_keep_goal true ctxt
      in autoref_monadic_tac ctxt end
    ))

  end

\<close> 
 "Automatic Refinement and Determinization for the Monadic Refinement Framework"

end
