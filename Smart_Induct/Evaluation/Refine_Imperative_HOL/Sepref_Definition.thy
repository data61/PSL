section \<open>Sepref-Definition Command\<close>
theory Sepref_Definition
imports Sepref_Rules "Lib/Pf_Mono_Prover" "Lib/Term_Synth"
keywords "sepref_definition" :: thy_goal
      and "sepref_thm" :: thy_goal
begin
subsection \<open>Setup of Extraction-Tools\<close>
  declare [[cd_patterns "hn_refine _ ?f _ _ _"]]

  lemma heap_fixp_codegen:
    assumes DEF: "f \<equiv> heap.fixp_fun cB"
    assumes M: "(\<And>x. mono_Heap (\<lambda>f. cB f x))"
    shows "f x = cB f x"
    unfolding DEF
    apply (rule fun_cong[of _ _ x])
    apply (rule heap.mono_body_fixp)
    apply fact
    done


  ML \<open>
    structure Sepref_Extraction = struct
      val heap_extraction: Refine_Automation.extraction = {
          pattern = Logic.varify_global @{term "heap.fixp_fun x"},
          gen_thm = @{thm heap_fixp_codegen},
          gen_tac = (fn ctxt => 
            Pf_Mono_Prover.mono_tac ctxt
          )
        }

      val setup = I 
        (*#> Refine_Automation.add_extraction "trivial" triv_extraction*)
        #> Refine_Automation.add_extraction "heap" heap_extraction

    end
    \<close>

  setup Sepref_Extraction.setup 


  subsection \<open>Synthesis setup for sepref-definition goals\<close>
  (* TODO: The UNSPEC are an ad-hoc hack to specify the synthesis goal *)
  consts UNSPEC::'a  

  abbreviation hfunspec 
    :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn)\<times>('a \<Rightarrow> 'b \<Rightarrow> assn)" 
    ("(_\<^sup>?)" [1000] 999)
    where "R\<^sup>? \<equiv> hf_pres R UNSPEC"

  definition SYNTH :: "('a \<Rightarrow> 'r nres) \<Rightarrow> (('ai \<Rightarrow>'ri Heap) \<times> ('a \<Rightarrow> 'r nres)) set \<Rightarrow> bool"
    where "SYNTH f R \<equiv> True"

  definition [simp]: "CP_UNCURRY _ _ \<equiv> True"
  definition [simp]: "INTRO_KD _ _ \<equiv> True"
  definition [simp]: "SPEC_RES_ASSN _ _ \<equiv> True"

  lemma [synth_rules]: "CP_UNCURRY f g" by simp
  lemma [synth_rules]: "CP_UNCURRY (uncurry0 f) (uncurry0 g)" by simp
  lemma [synth_rules]: "CP_UNCURRY f g \<Longrightarrow> CP_UNCURRY (uncurry f) (uncurry g)" by simp

  lemma [synth_rules]: "\<lbrakk>INTRO_KD R1 R1'; INTRO_KD R2 R2'\<rbrakk> \<Longrightarrow> INTRO_KD (R1*\<^sub>aR2) (R1'*\<^sub>aR2')" by simp
  lemma [synth_rules]: "INTRO_KD (R\<^sup>?) (hf_pres R k)" by simp
  lemma [synth_rules]: "INTRO_KD (R\<^sup>k) (R\<^sup>k)" by simp
  lemma [synth_rules]: "INTRO_KD (R\<^sup>d) (R\<^sup>d)" by simp

  lemma [synth_rules]: "SPEC_RES_ASSN R R" by simp
  lemma [synth_rules]: "SPEC_RES_ASSN UNSPEC R" by simp
  
  lemma synth_hnrI:
    "\<lbrakk>CP_UNCURRY fi f; INTRO_KD R R'; SPEC_RES_ASSN S S'\<rbrakk> \<Longrightarrow> SYNTH_TERM (SYNTH f ([P]\<^sub>a R\<rightarrow>S)) ((fi,SDUMMY)\<in>SDUMMY,(fi,f)\<in>([P]\<^sub>a R'\<rightarrow>S'))" 
    by (simp add: SYNTH_def)

term starts_with

ML \<open>
  structure Sepref_Definition = struct
    fun make_hnr_goal t ctxt = let
      val ctxt = Variable.declare_term t ctxt
      val (pat,goal) = case Term_Synth.synth_term @{thms synth_hnrI} ctxt t of
        @{mpat "(?pat,?goal)"} => (pat,goal) | t => raise TERM("Synthesized term does not match",[t])
      val pat = Thm.cterm_of ctxt pat |> Refine_Automation.prepare_cd_pattern ctxt
      val goal = HOLogic.mk_Trueprop goal
    in
      ((pat,goal),ctxt)
    end

    val cfg_prep_code = Attrib.setup_config_bool @{binding sepref_definition_prep_code} (K true)

    local 
      open Refine_Util
      val flags = parse_bool_config' "prep_code" cfg_prep_code
      val parse_flags = parse_paren_list' flags  

    in       
      val sd_parser = parse_flags -- Parse.binding -- Parse.opt_attribs --| @{keyword "is"} 
        -- Parse.term --| @{keyword "::"} -- Parse.term
    end  

    fun mk_synth_term ctxt t_raw r_raw = let
        val t = Syntax.parse_term ctxt t_raw
        val r = Syntax.parse_term ctxt r_raw
        val t = Const (@{const_name SYNTH},dummyT)$t$r
      in
        Syntax.check_term ctxt t
      end  


    fun sd_cmd ((((flags,name),attribs),t_raw),r_raw) lthy = let
      local
        val ctxt = Refine_Util.apply_configs flags lthy
      in
        val flag_prep_code = Config.get ctxt cfg_prep_code
      end

      val t = mk_synth_term lthy t_raw r_raw

      val ((pat,goal),ctxt) = make_hnr_goal t lthy
      
      fun 
        after_qed [[thm]] ctxt = let
            val thm = singleton (Variable.export ctxt lthy) thm

            val (_,lthy) 
              = Local_Theory.note 
                 ((Refine_Automation.mk_qualified (Binding.name_of name) "refine_raw",[]),[thm]) 
                 lthy;

            val ((dthm,rthm),lthy) = Refine_Automation.define_concrete_fun NONE name attribs [] thm [pat] lthy

            val lthy = lthy 
              |> flag_prep_code ? Refine_Automation.extract_recursion_eqs 
                [Sepref_Extraction.heap_extraction] (Binding.name_of name) dthm

            val _ = Thm.pretty_thm lthy dthm |> Pretty.string_of |> writeln
            val _ = Thm.pretty_thm lthy rthm |> Pretty.string_of |> writeln
          in
            lthy
          end
        | after_qed thmss _ = raise THM ("After-qed: Wrong thmss structure",~1,flat thmss)

    in
      Proof.theorem NONE after_qed [[ (goal,[]) ]] ctxt
    end



    val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "sepref_definition"}
      "Synthesis of imperative program"
      (sd_parser >> sd_cmd)

    val st_parser = Parse.binding --| @{keyword "is"} -- Parse.term --| @{keyword "::"} -- Parse.term

    fun st_cmd ((name,t_raw),r_raw) lthy = let
      val t = mk_synth_term lthy t_raw r_raw
      val ((_,goal),ctxt) = make_hnr_goal t lthy
      
      fun 
        after_qed [[thm]] ctxt = let
            val thm = singleton (Variable.export ctxt lthy) thm

            val _ = Thm.pretty_thm lthy thm |> Pretty.string_of |> tracing
  
            val (_,lthy) 
              = Local_Theory.note 
                 ((Refine_Automation.mk_qualified (Binding.name_of name) "refine_raw",[]),[thm]) 
                 lthy;

          in
            lthy
          end
        | after_qed thmss _ = raise THM ("After-qed: Wrong thmss structure",~1,flat thmss)

    in
      Proof.theorem NONE after_qed [[ (goal,[]) ]] ctxt
    end

    val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "sepref_thm"}
      "Synthesis of imperative program: Only generate raw refinement theorem"
      (st_parser >> st_cmd)

  end
\<close>

end
