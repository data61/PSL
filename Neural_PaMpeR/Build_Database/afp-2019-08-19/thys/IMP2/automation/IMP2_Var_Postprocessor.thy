section \<open>Program Variables to Isabelle Variables\<close>
theory IMP2_Var_Postprocessor
imports "../basic/Semantics" "../parser/Parser" "../lib/Subgoal_Focus_Some"
begin
  definition RENAMING :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    where "RENAMING s d \<equiv> s = d"
    
  lemma RENAMINGD: "RENAMING s d \<Longrightarrow> s = d" unfolding RENAMING_def by auto
  lemma RENAMINGI:
    assumes "\<And>d. RENAMING s d \<Longrightarrow> P"
    shows "P" using assms
    unfolding RENAMING_def by simp
    
  ML \<open>
    structure Renaming = struct
      fun RENAMING_rl ctxt (s,d) = let
        (* FIXME: Rough approximation to hit \<And>d. \<dots> *)
        fun rn (Abs ("d",T,t)) = Abs (d,T,t)
          | rn (a$b) = rn a $ rn b
          | rn t = t
    
        val s = Thm.cterm_of ctxt s
          
        val thm = @{thm RENAMINGI}
          |> Drule.infer_instantiate' ctxt [SOME s]
        
        val t = thm  |> Thm.prop_of |> rn
        val thm' = Thm.renamed_prop t thm
      in thm' end
  
      
      fun apply_renamings_tac ctxt = let
        fun is_renaming (Const (@{const_name RENAMING},_)$_$_) = true | is_renaming _ = false
      in 
        Subgoal_Focus_Some.FOCUS_SOME_PREMS (fn _ => Thm.term_of #> HOLogic.dest_Trueprop #> is_renaming)
          (fn {context=ctxt, prems, ...} => let 
            val thms = map (fn t => @{thm RENAMINGD} OF [t]) prems
          in 
            Local_Defs.unfold_tac ctxt thms end) ctxt
      
      end
      
      
      fun remove_renamings_tac ctxt = let 
        (* TODO: Unsafe. Should check that source does not occur elsewhere in goal! *)
      in
        SELECT_GOAL (
          REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt @{thms thin_rl[of "RENAMING _ _"]})
            THEN Local_Defs.unfold_tac ctxt @{thms triv_forall_equality}
          ))
      end
      
      
    end
  \<close>  

  method_setup i_vcg_apply_renamings_tac = \<open>Scan.succeed (SIMPLE_METHOD' o Renaming.apply_renamings_tac)\<close>
  method_setup i_vcg_remove_renamings_tac = \<open>Scan.succeed (SIMPLE_METHOD' o Renaming.remove_renamings_tac)\<close>
      

  definition NAMING_HINT :: "state \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where "NAMING_HINT s x n \<equiv> True"  
    
          
  ML \<open>
    (*
      Postprocess VCs to convert states applied to variable names to actual logical variables.
    *)
    structure VC_Postprocessor = struct
    
      (* Guess suffix from name, e.g. "a\<^sub>3" \<mapsto> "\<^sub>3" *)  
      val guess_suffix = let
        val sfxs = ["'","\<^sub>","\<^sup>","\<^bsub>","\<^bsup>"]
      in  
        Symbol.explode #> chop_prefix (not o member op = sfxs) #> snd #> implode
      end
    
      fun guess_renaming param_rename_tab ((s,x),(kind,vname)) = let

        fun name_of (Free (n,_)) = n
          | name_of _ = "v"
            
        val sname = the_default (name_of s) (Termtab.lookup param_rename_tab s)
      
        val sfx = guess_suffix sname
        val src = case kind of
          IMP_Syntax.ARRAY => s$x | IMP_Syntax.VAL => s$x$ @{term "0::int"}
      
        val dst = suffix sfx vname
      in
        (src,dst)
      end
      
      
      structure Candtab = Table(type key = term*term val ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord)
      
      fun add_state_candidates ((s as Free (_,@{typ state})) $ x) = (
        case try HOLogic.dest_string x of
          SOME vname => apfst (Candtab.update ((s,x),(IMP_Syntax.ARRAY,vname)))
        | NONE => apsnd (insert op= s) #> add_state_candidates x  
      )
      | add_state_candidates ((s as Free (_,@{typ state})) $ x $ @{term "0::int"}) = (
        case try HOLogic.dest_string x of
          SOME vname => apfst (Candtab.default ((s,x),(IMP_Syntax.VAL,vname)))
        | NONE => apsnd (insert op= s) #> add_state_candidates x  
      )
      | add_state_candidates (s as Free (_,@{typ state})) = apsnd (insert op= s)
      | add_state_candidates (a$b) = add_state_candidates a #> add_state_candidates b
      | add_state_candidates (Abs (_,_,t)) = add_state_candidates t
      | add_state_candidates _ = I
      
      fun hint_renaming hint_tab (rn as (sx,(kind,_))) = case Candtab.lookup hint_tab sx of
        NONE => rn
      | SOME vname' => (sx,(kind,vname'))
      
      fun compute_renamings param_rename_tab hint_tab (good,bad) = 
        subtract (fn (bs, ((s,_),_)) => bs=s) bad (Candtab.dest good)
      |> map (hint_renaming hint_tab)  
      |> map (guess_renaming param_rename_tab)
      
      (* Naming hints go to hint-tab in #1, other premises go to list in #2 *)
      fun add_naming_hint (@{const Trueprop}$(@{const NAMING_HINT}$s$x$n)) = (case try HOLogic.dest_string n of
          SOME n => apfst (Candtab.update ((s,x),n))
        | NONE => (warning "NAMING_HINT with non-string constant ignored"; I)
        )
      | add_naming_hint t = apsnd (cons t)
      
      
      val insert_vbind_tac = Subgoal.FOCUS_PREMS (fn {context=ctxt, concl, params, prems, ...} => let
          val conclt = Thm.term_of concl
          
          val param_rename_tab = params |> map (apsnd (Thm.term_of) #> swap) |> Termtab.make 
          
          val (hint_tab,prem_ts) = 
            fold (add_naming_hint o Thm.prop_of) prems (Candtab.empty,[]) 
          
          (* val _ = @{print} (hint_tab,prem_ts)  *)
            
          val renamings = 
              add_state_candidates conclt (Candtab.empty,[]) 
            |> fold (add_state_candidates) prem_ts
            |> compute_renamings param_rename_tab hint_tab
            
          val tacs = map (resolve_tac ctxt o single o Renaming.RENAMING_rl ctxt) renamings
        in
          EVERY1 tacs
        end
        )
      
      fun remove_tac ctxt = let 
        (* TODO: Unsafe. Should check that source does not occur elsewhere in goal! *)
      in
        SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt @{thms thin_rl[of "NAMING_HINT _ _ _"]})))
        THEN' Renaming.remove_renamings_tac ctxt
      end
        
        
      fun postprocess_vc_tac ctxt =
        insert_vbind_tac ctxt
        THEN' Renaming.apply_renamings_tac ctxt
        THEN' remove_tac ctxt
  
    end
  \<close>  
  
  method_setup i_vcg_insert_vbind_tac = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.insert_vbind_tac)\<close>
  method_setup i_vcg_postprocess_vars = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.postprocess_vc_tac)\<close>

end
