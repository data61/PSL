theory Synth_Definition
imports "Automatic_Refinement.Refine_Lib" "HOL-Library.Rewrite"
  "Refine_Imperative_HOL.Sepref_Misc" (* FIXME: Some stuff we depend on has not yet been moved out from there! *)
keywords "synth_definition" :: thy_goal
begin


ML \<open>
  (*
    Provides the command synth_definition, which proves a schematic goal with a hole, and defines
    the hole as a constant.
  *)
  structure Synth_Definition = struct
    (*val cfg_prep_code = Attrib.setup_config_bool @{binding synth_definition_prep_code} (K false)*)
      
    local 
      open Refine_Util
      (*val flags = parse_bool_config' "prep_code" cfg_prep_code
      val parse_flags = parse_paren_list' flags  *)

    in       
      val sd_parser = (*parse_flags --*) Parse.binding -- Parse.opt_attribs --| @{keyword "is"} 
        -- Scan.optional (Parse.attribs --| Parse.$$$ ":") [] -- Parse.term 
    end  

    fun prep_term t = let
      val nidx = maxidx_of_term t + 1
    
      val t = map_aterms (fn 
            @{mpat (typs) "\<hole>::?'v_T"} => Var (("HOLE",nidx),T)
          | v as Var ((name,_),T) => if String.isPrefix "_" name then v else Var (("_"^name,nidx),T)
          | t => t
        ) t
      |> Term_Subst.zero_var_indexes
    
    in
      t
    end


    fun sd_cmd (((name,attribs_raw),attribs2_raw),t_raw) lthy = let
      local
        (*val ctxt = Refine_Util.apply_configs flags lthy*)
      in
        (*val flag_prep_code = Config.get ctxt cfg_prep_code*)
      end

      val read = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern lthy)
      
      val t = t_raw |> read |> prep_term
      val ctxt = Variable.declare_term t lthy
      val pat= Thm.cterm_of ctxt t
      val goal=t

      val attribs2 = map (Attrib.check_src lthy) attribs2_raw;
      
      
      fun 
        after_qed [[thm]] ctxt = let
            val thm = singleton (Variable.export ctxt lthy) thm

            val (_,lthy) 
              = Local_Theory.note 
                 ((Refine_Automation.mk_qualified (Binding.name_of name) "refine_raw",[]),[thm]) 
                 lthy;

            val ((dthm,rthm),lthy) = Refine_Automation.define_concrete_fun NONE name attribs_raw [] thm [pat] lthy

            val (_,lthy) = Local_Theory.note ((Binding.empty,attribs2),[rthm]) lthy
            
            (* FIXME: Does not work, as we cannot see the default extraction patterns!
            val lthy = lthy 
              |> flag_prep_code ? Refine_Automation.extract_recursion_eqs 
                [Sepref_Extraction.heap_extraction] (Binding.name_of name) dthm
            *)

            val _ = Thm.pretty_thm lthy dthm |> Pretty.string_of |> writeln
            val _ = Thm.pretty_thm lthy rthm |> Pretty.string_of |> writeln
          in
            lthy
          end
        | after_qed thmss _ = raise THM ("After-qed: Wrong thmss structure",~1,flat thmss)

    in
      Proof.theorem NONE after_qed [[ (goal,[]) ]] ctxt
    end



    val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "synth_definition"}
      "Synthesis of constant"
      (sd_parser >> sd_cmd)
      
  end
\<close>


end
