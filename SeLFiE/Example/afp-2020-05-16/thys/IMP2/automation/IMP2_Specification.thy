section \<open>Specification Commands\<close>
theory IMP2_Specification 
imports IMP2_Basic_Simpset IMP2_Program_Analysis IMP2_Var_Postprocessor IMP2_Var_Abs
keywords "ensures"
     and "returns" "variant" "relation"
     and "program_spec" :: thy_goal
     and "procedure_spec" :: thy_goal
     and "recursive_spec" :: thy_goal
begin

  
subsection \<open>Abstraction over Program Variables\<close>

lemmas [named_ss vcg_bb cong] = refl[of "ANNOTATION _"]


ML \<open> structure IMP_Annotations 
  = struct
    fun strip_annotations ctxt = 
      Local_Defs.unfold ctxt (Named_Theorems.get ctxt @{named_theorems vcg_annotation_defs})
    
    fun strip_annotations_term ctxt = 
      Thm.cterm_of ctxt #> Drule.mk_term #> 
      strip_annotations ctxt #>
      Drule.dest_term #> Thm.term_of

    fun mk_ANNOTATION t = let val T=fastype_of t in 
      Const (@{const_name ANNOTATION}, T --> T)$t end 
      
    fun dest_ANNOTATION (Const (@{const_name ANNOTATION}, _)$t) = t
      | dest_ANNOTATION t = raise TERM("dest_ANNOTATION", [t]);
      
    
    (* Provides a context for reading the term, and a postprocessing function *)
    type term_annot_reader = Proof.context * (term -> term)  
    fun gen_read_ta rd ((ctxt,post):term_annot_reader) src = rd ctxt src |> mk_BB_PROTECT |> post
    val read_ta_from_cartouche = gen_read_ta Term_Annot.read_term

    (* Annotations *)
    
    type cmd_annotation_readers = {
      rel_rd : term_annot_reader,
      variant_rd : term_annot_reader,
      invar_rd : term_annot_reader,
      com_post: term -> term
    }
    
          
    fun gen_interpret_annotations (annot_readers : cmd_annotation_readers) ctxt prog_t = let
    
      (* TODO/FIXME: Terms are read independently, which will cause too generic types to be inferred *)

      val read_invar = read_ta_from_cartouche (#invar_rd annot_readers)
      val read_variant = read_ta_from_cartouche (#variant_rd annot_readers)
      val read_rel = read_ta_from_cartouche (#rel_rd annot_readers)
          
      val mpt = map_types (map_type_tfree (K dummyT))
      
      fun interp_while_annot (t,@{syntax_const "_invariant_annotation"}) (R,V,I) = (R,V,read_invar t :: I)
        | interp_while_annot (t,@{syntax_const "_variant_annotation"})   (R,V,I) = (R,read_variant t :: V,I)
        | interp_while_annot (t,@{syntax_const "_relation_annotation"})  (R,V,I) = (read_rel t :: R,V,I)
        | interp_while_annot (_,ty) _ = error ("Unknown annotation type for while loop: " ^ ty)
      
      fun interp_while_annots annots = let
        val annots = HOLogic.strip_tuple annots
          |> map (apsnd (dest_Const #> fst) o Term_Annot.dest_annotated_term)
          
        val (Rs,Vs,Is) = fold interp_while_annot annots ([],[],[])
         
        val _ = length Rs > 1 andalso error "Multiple relation annotations to loop"
        val _ = length Vs > 1 andalso error "Multiple variant annotations to loop"
        val _ = length Is > 1 andalso error "Multiple invariants not yet supported. Combine them into one"
         
        local val m = map mk_ANNOTATION in
          val (Rs, Vs, Is) = (m Rs, m Vs, m Is)
        end
        
        
      in 
        case (Rs,Vs,Is) of
          ([],[],[]) => mpt @{const While}
        | ([],[],[I]) => mpt @{const WHILE_annotI} $ I
        | ([],[V],[I]) => mpt @{const WHILE_annotVI} $ V $ I
        | ([R],[V],[I]) => mpt @{const WHILE_annotRVI ('a)} $ R $ V $ I
        | _ => error "Illegal combination of annotations to while loop. The legal ones are: None, I, VI, RVI"
      
      end
      
      fun interp (Const (@{const_abbrev While_Annot},_)$annots) = interp_while_annots annots
        | interp (a$b) = interp a $ interp b
        | interp (Abs (x,T,t)) = Abs (x,T,interp t)
        | interp t = t
    
        
      val prog_t = interp prog_t

      (* All terms have been abstracted over vinfo, and over the variables of v0info. 
        Now, the whole term is valid wrt vinfo0/ctxt0, which contains declarations 
        of variables0 and state0
        *** TODO: Ideally, one would like to check teh term in a context that does not include 
              variables, but only state decl!
      *)      
      val prog_t = Syntax.check_term ctxt prog_t
      
            
      (* We now also abstract over state0, to make the program a function from state0 to an (annotated) command *)
      val res = (#com_post annot_readers) prog_t

      (*
      (* Alternatively, we strip the annotations from the program. This should also remove state0! *)
      val prog_t = strip_annotations_term ctxt prog_t
      *)
      
    in
      res
    end


    (*
      Make a reader according to a list of program variable abstractions.
      Each list item has the form (vars,sfx,full), where vars is a list of IMP variables,
      sfx is a suffix to be appended to the Isabelle variables, and full indicates whether the
      abstraction over the state should be done immediately, or delayed.
      
      The result is a reader, and a second term transformation to do the delayed abstractions.
    *)
    fun gen_mk_reader rds ctxt = let
      fun mk [] ctxt = ((ctxt, I), I)
        | mk ((vars,sfx,full)::rds) ctxt = let
            val vars = IMP_Parser.merge_variables vars
            val (vinfo,ctxt) = Program_Variables.declare_variables vars sfx ctxt
            val ((ctxt,pps1),pps2) = mk rds ctxt
                        
            val absv = Program_Variables.abstract_vars vinfo
            val abss = Program_Variables.abstract_state vinfo
            
            val (pps1,pps2) = if full then (absv #> pps1 #> abss,pps2) else (absv #> pps1, pps2 #> abss)
          in
            ((ctxt,pps1),pps2)
          end
          
    in
      mk rds ctxt
    end

    type rd_config = {
      add_vars  : IMP_Syntax.impvar list,           (* Additional variable declarations *)
      in_vars   : string list option,               (* Input variables: Default all vars *)
      out_vars  : string list option,               (* Output variables: Default all vars *)
      prog_vars : IMP_Syntax.impvar list            (* Variables in program *)
    }
    
        
    local  
      fun vars_dflt (cfg:rd_config) NONE = (#prog_vars cfg) @ (#add_vars cfg)
        | vars_dflt (cfg:rd_config) (SOME vs) = let
            val (gvs,lvs) = List.partition (IMP_Syntax.is_global) vs
            val _ = if gvs <> [] then 
              Pretty.block [Pretty.str "Ignoring global parameter/return variables: ",
                            Pretty.list "" "" (map (Pretty.str) gvs)]
              |> Pretty.string_of |> warning             
            else () 
        
          in
            (filter (fst #> member op= lvs) (#prog_vars cfg @ #add_vars cfg ))
          @ (filter (fst #> IMP_Syntax.is_global) (#add_vars cfg))  
          end
       
      fun cfg_in_vars cfg = vars_dflt cfg (#in_vars cfg)
      fun cfg_out_vars cfg = vars_dflt cfg (#out_vars cfg)
        
    in        
      (* Standard annotation readers *)
      
      
      fun mk_annot_readers (cfg:rd_config) ctxt = let
        val in_vars = cfg_in_vars cfg
        val prog_vars = (#prog_vars cfg) @ (#add_vars cfg)
        
        val (rel_rd,_) = gen_mk_reader [] ctxt
        val (annot_rd,post) = gen_mk_reader [(in_vars,"\<^sub>0",false),(prog_vars,"",true)] ctxt
      in 
        { 
          rel_rd = rel_rd,
          variant_rd = annot_rd,
          invar_rd = annot_rd,
          com_post = post
        }
      end
        
      fun mk_pre_reader cfg ctxt = gen_mk_reader [(cfg_in_vars cfg,"",true)] ctxt |> #1
        
      fun mk_post_reader cfg ctxt = let
        val in_vars = cfg_in_vars cfg
        val out_vars = cfg_out_vars cfg
      in
        gen_mk_reader [(in_vars,"\<^sub>0",true),(out_vars,"",true)] ctxt |> #1
      end  
  
      fun mk_variant_reader cfg ctxt = let
        val in_vars = cfg_in_vars cfg
      in
        gen_mk_reader [(in_vars,"",true)] ctxt |> #1
      end

      fun read_program cfg ctxt prog_t = 
        gen_interpret_annotations (mk_annot_readers cfg ctxt) ctxt prog_t
  
      
    end            
    
  end
\<close>



subsection \<open>Hoare Triple Syntax\<close>
  
(* In-Term notation for Hoare Triples*)   
syntax "_Htriple" :: "cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> logic" ("\<^htriple>_ _ _")
syntax "_Htriple_Partial" :: "cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> logic" ("\<^htriple_partial>_ _ _")


ML \<open> structure VCG_Htriple_Syntax 
  = struct
    
    fun mk_htriple' total env (pre,prog_t,post) = let    
      (* Assemble Hoare-triple *)
      val HT_const = if total then @{const HT'} else @{const HT'_partial}
      val res = HT_const$ env $pre$prog_t$post
    in
      res
    end
    
    fun decon_cartouche_ast ((c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p) = (
      case Term_Position.decode_position p of 
        SOME (pos, _) => ((s,pos) (*, fn t => c$t$p*))
      | NONE => raise TERM ("cartouche with invalid pos",[c,p])  
    )
    | decon_cartouche_ast t = raise TERM ("decon_cartouche_ast",[t])  
        
    
    fun htriple_tr total ctxt [tpre, prog_t, tpost] = let
      open IMP_Annotations
    
      val (vars,prog_t) = decon_cartouche_ast prog_t |> IMP_Parser.parse_command_at ctxt
      
      val cfg = { add_vars = [], in_vars=NONE, out_vars=NONE, prog_vars=vars }
      
      val prog_t = read_program cfg ctxt prog_t
        
      val tpre = decon_cartouche_ast tpre 
        |> read_ta_from_cartouche (mk_pre_reader cfg ctxt)
        
      val tpost = decon_cartouche_ast tpost
        |> read_ta_from_cartouche (mk_post_reader cfg ctxt)

      val res = mk_htriple' total @{term "Map.empty :: program"} (tpre,prog_t,tpost)  
              
    in 
      IMP_Parser.mark_term res |> @{print}
    end
    | htriple_tr _ _ args = raise TERM ("htriple_tr", args)
      
    
  end
\<close>
  
parse_translation \<open>[
  (@{syntax_const "_Htriple"}, VCG_Htriple_Syntax.htriple_tr true),
  (@{syntax_const "_Htriple_Partial"}, VCG_Htriple_Syntax.htriple_tr false)
  ]
\<close>
   
term \<open>\<^htriple_partial> \<open>undefined x :: bool\<close> \<open>while (n\<noteq>0) @invariant \<open>x=1+undefined+n+foo\<close> n = n - 1; x=x+1\<close> \<open>True\<close>\<close> 

term \<open>\<^htriple_partial> \<open>n\<ge>0+x+notex\<close> \<open>while (n\<noteq>0) n = n - 1; x=x+1\<close> \<open>n=0 \<and> x=1+x\<^sub>0\<close>\<close> 
term \<open>\<^htriple> \<open>n\<ge>0+x+notex\<close> \<open>while (n\<noteq>0) n = n - 1; x=x+1\<close> \<open>n=0 \<and> x=1+x\<^sub>0\<close>\<close>


subsection \<open>Postprocessing of Proved Specifications\<close>

subsubsection \<open>Modified Sets\<close>
  
lemma HT_to_mod: "HT \<pi> P c Q = HT_mods \<pi> (ANALYZE (lhsv \<pi> c)) P c Q"
  by (auto simp: HT_mods_def BB_PROTECT_def HT_def intro: wp_strengthen_modset wp_conseq)

lemma HT_partial_to_mod: "HT_partial \<pi> P c Q = HT_partial_mods \<pi> (ANALYZE (lhsv \<pi> c)) P c Q"
  by (auto simp: HT_partial_mods_def BB_PROTECT_def HT_partial_def intro: wlp_strengthen_modset wlp_conseq)

lemma mk_lhsv_thm:  
  assumes "c \<equiv> cmd"
  shows "lhsv \<pi> c = ANALYZE (lhsv \<pi> cmd)" "lhsv' c = ANALYZE (lhsv' cmd)"
  using assms by simp_all
  
  ML \<open> structure IMP2_Modified_Analysis 
    = struct
      fun dest_HT_mods (Const (@{const_name HT_mods},_)$pi$mods$P$c$Q) = (true,pi,mods,P,c,Q)
        | dest_HT_mods (Const (@{const_name HT_partial_mods},_)$pi$mods$P$c$Q) = (false,pi,mods,P,c,Q)
        | dest_HT_mods t = raise TERM("dest_HT_mods",[t])
          

      (* Valid modset must be set literal of string literals *)
      val is_valid_modset = can (HOLogic.dest_set #> map HOLogic.dest_string)
        
      (* Weaker criterion for valid modset  
      val is_valid_modset = not o exists_subterm (fn @{const lhsv} => true | _ => false)
      *)
      
                
         
      (* HT \<rightarrow> HT_mods *) 
      fun mk_HT_mods ctxt thm = let
        (* Local_Defs.unfold will destroy names of bound variables here!?, so using simplify! *)
        fun simplified ctxt thms = simplify (Simplifier.clear_simpset ctxt addsimps thms)
      
        val ctxt = Named_Simpsets.put @{named_simpset vcg_bb} ctxt
      in
           thm
        |> simplified ctxt @{thms HT_to_mod HT_partial_to_mod}
        |> Simplifier.simplify ctxt
      end    

      
      (* c\<equiv>com \<rightarrow> [ lhsv c = \<dots>, lshv' c = \<dots> ] *)
      fun mk_lhsv_thms ctxt def_thm = let
        val ctxt = Named_Simpsets.put @{named_simpset vcg_bb} ctxt
      in
        map (fn thm => (def_thm RS thm) |> Simplifier.simplify ctxt) @{thms mk_lhsv_thm}
      end
      
    end
  \<close>
  
  
  
subsubsection \<open>Parameter Passing\<close>  
(* Forward assignment rule + renaming of assigned variable *)  
lemma adjust_assign_after:
  assumes "HT \<pi> P c Q"
  shows "HT \<pi> P (c;;x[]::=y) (\<lambda>s\<^sub>0 s. \<exists>vx. Q s\<^sub>0 (s(x:=vx,y:=s x)))"  
  using assms unfolding HT_def
  apply (auto simp: wp_eq[abs_def])
  by (metis (mono_tags, lifting) fun_upd_triv wp_conseq)

(* Standard backwards assignment rule *)
lemma adjust_assign_before:
  assumes HT: "HT \<pi> P c Q"  
  shows "HT \<pi> (\<lambda>s. P (s(x:=s y)) ) (x[]::=y;; c) (\<lambda>s\<^sub>0 s. Q (s\<^sub>0(x:=s\<^sub>0 y)) s)"
  unfolding HT_def
  apply (clarsimp simp: wp_eq)  
  using HT_def assms by auto
    
  
(* Forward + backward assignment rules, simultaneously for all local variables! *)
lemma adjust_scope:
  assumes HT: "HT \<pi> P c Q"
  shows "HT \<pi> (\<lambda>s. P (<<>|s>)) (SCOPE c) (\<lambda>s\<^sub>0 s. \<exists>l. Q (<<>|s\<^sub>0>) (<l|s>))"
  unfolding HT_def
  apply (clarsimp simp: wp_eq)  
  by (smt HT_def assms combine_collapse combine_nest(1) wp_conseq)

  
(* Forward assignment rule + renaming of assigned variable *)  
lemma adjust_assign_after_partial:
  assumes "HT_partial \<pi> P c Q"
  shows "HT_partial \<pi> P (c;;x[]::=y) (\<lambda>s\<^sub>0 s. \<exists>vx. Q s\<^sub>0 (s(x:=vx,y:=s x)))"  
  using assms unfolding HT_partial_def
  apply (auto simp: wlp_eq[abs_def])
  by (metis (mono_tags, lifting) fun_upd_triv wlp_conseq)

(* Standard backwards assignment rule *)
lemma adjust_assign_before_partial:
  assumes HT: "HT_partial \<pi> P c Q"  
  shows "HT_partial \<pi> (\<lambda>s. P (s(x:=s y)) ) (x[]::=y;; c) (\<lambda>s\<^sub>0 s. Q (s\<^sub>0(x:=s\<^sub>0 y)) s)"
  unfolding HT_partial_def
  apply (clarsimp simp: wlp_eq)  
  using HT_partial_def assms by auto
    
  
(* Forward + backward assignment rules, simultaneously for all local variables! *)
lemma adjust_scope_partial:
  assumes HT: "HT_partial \<pi> P c Q"
  shows "HT_partial \<pi> (\<lambda>s. P (<<>|s>)) (SCOPE c) (\<lambda>s\<^sub>0 s. \<exists>l. Q (<<>|s\<^sub>0>) (<l|s>))"
  unfolding HT_partial_def
  apply (clarsimp simp: wlp_eq)  
  by (smt HT_partial_def assms combine_collapse combine_nest(1) wlp_conseq)
    

definition "ADJUST_PRE_SCOPE P \<equiv> (\<lambda>s. P <<>|s>)"
definition "ADJUST_PRE_PARAM l G P \<equiv> (\<lambda>s. P (s(l:=s G)))"
definition "ADJUST_POST_SCOPE Q \<equiv> (\<lambda>s\<^sub>0 s. \<exists>l. Q (<<>|s\<^sub>0>) (<l|s>))"
definition "ADJUST_POST_PARAM l G Q \<equiv> (\<lambda>s\<^sub>0 s. Q (s\<^sub>0(l:=s\<^sub>0 G)) s)"
definition "ADJUST_POST_RETV G l Q \<equiv> (\<lambda>s\<^sub>0 s. \<exists>vx. Q s\<^sub>0 (s(G:=vx,l:=s G)))"

  
lemma HT_strengthen_modset:  
  assumes "HT \<pi> P c Q"
  shows "HT \<pi> P c (\<lambda>s\<^sub>0 s. Q s\<^sub>0 s \<and> modifies (lhsv \<pi> c) s s\<^sub>0)"
  using assms unfolding HT_def by (auto intro: wp_strengthen_modset)

lemma HT_partial_strengthen_modset:  
  assumes "HT_partial \<pi> P c Q"
  shows "HT_partial \<pi> P c (\<lambda>s\<^sub>0 s. Q s\<^sub>0 s \<and> modifies (lhsv \<pi> c) s s\<^sub>0)"
  using assms unfolding HT_partial_def by (auto intro: wlp_strengthen_modset)
      
    
context
  notes [abs_def, simp] = VAR_def 
    ADJUST_PRE_SCOPE_def ADJUST_PRE_PARAM_def ADJUST_POST_SCOPE_def ADJUST_POST_PARAM_def ADJUST_POST_RETV_def
  notes [simp] = combine_query
begin

  text \<open>A lot of straightforward lemmas, to transfer specification of function body to function specification\<close>
  
  lemma ADJUST_PRE_SCOPE_unfolds:
    "\<And>P. ADJUST_PRE_SCOPE (\<lambda>_. P) = (\<lambda>_. P)"
    "\<And>P. ADJUST_PRE_SCOPE (\<lambda>s. VAR v (\<lambda>x. P x s)) = VAR v (\<lambda>x. ADJUST_PRE_SCOPE (\<lambda>s. P x s))"
    
    "\<And>P. is_global x \<Longrightarrow> ADJUST_PRE_SCOPE (\<lambda>s. VAR (s x i) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s x i) (\<lambda>x. ADJUST_PRE_SCOPE (\<lambda>s. P x s) s))"
    "\<And>P. is_global x \<Longrightarrow> ADJUST_PRE_SCOPE (\<lambda>s. VAR (s x) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s x) (\<lambda>x. ADJUST_PRE_SCOPE (\<lambda>s. P x s) s))"
    by auto
  
  lemma ADJUST_PRE_PARAM_unfolds:  
    "\<And>P. ADJUST_PRE_PARAM l G (\<lambda>_. P) = (\<lambda>_. P)"
    "\<And>P. ADJUST_PRE_PARAM l G (\<lambda>s. VAR v (\<lambda>x. P x s)) = VAR v (\<lambda>x. ADJUST_PRE_PARAM l G (\<lambda>s. P x s))"
    
    
    "\<And>P. ADJUST_PRE_PARAM l G (\<lambda>s. VAR (s l i) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s G i) (\<lambda>x. ADJUST_PRE_PARAM l G (\<lambda>s. P x s) s))"
    "\<And>P. ADJUST_PRE_PARAM l G (\<lambda>s. VAR (s l) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s G) (\<lambda>x. ADJUST_PRE_PARAM l G (\<lambda>s. P x s) s))"
    
    "\<And>P. x\<noteq>l \<Longrightarrow> ADJUST_PRE_PARAM l G (\<lambda>s. VAR (s x i) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s x i) (\<lambda>x. ADJUST_PRE_PARAM l G (\<lambda>s. P x s) s))"
    "\<And>P. x\<noteq>l \<Longrightarrow> ADJUST_PRE_PARAM l G (\<lambda>s. VAR (s x) (\<lambda>x. P x s)) = (\<lambda>s. VAR (s x) (\<lambda>x. ADJUST_PRE_PARAM l G (\<lambda>s. P x s) s))"
    by auto
    
  lemma ADJUST_POST_SCOPE_unfolds:
    "\<And>P. ADJUST_POST_SCOPE (\<lambda>_ _. P) = (\<lambda>_ _. P)"
    
    "\<And>P. is_global x \<Longrightarrow> ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. is_global x \<Longrightarrow> ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    
    "\<And>P. is_global x \<Longrightarrow> ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. is_global x \<Longrightarrow> ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. ADJUST_POST_SCOPE (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    by auto
  
  lemma ADJUST_POST_PARAM_unfolds: 
    "\<And>P. ADJUST_POST_PARAM l G (\<lambda>_ _. P) = (\<lambda>_ _. P)" 
    
    "\<And>P. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 l i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 G i) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 l) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 G) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
  
    "\<And>P. x\<noteq>l \<Longrightarrow> ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. x\<noteq>l \<Longrightarrow> ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    
    "\<And>P. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. ADJUST_POST_PARAM l G (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    by auto
        
  lemma ADJUST_POST_RETV_unfolds:
    "\<And>P. ADJUST_POST_RETV G l (\<lambda>_ _. P) = (\<lambda>_ _. P)"
    
    "\<And>P. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x i) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s\<^sub>0 x) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
  
    "\<And>P. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s l i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s G i) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s l) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s G) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
      
    "\<And>P. \<lbrakk>x\<noteq>G; x\<noteq>l\<rbrakk> \<Longrightarrow> ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x i) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    "\<And>P. \<lbrakk>x\<noteq>G; x\<noteq>l\<rbrakk> \<Longrightarrow> ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. P x s\<^sub>0 s)) = (\<lambda>s\<^sub>0 s. VAR (s x) (\<lambda>x. ADJUST_POST_RETV G l (\<lambda>s\<^sub>0 s. P x s\<^sub>0 s) s\<^sub>0 s))"
    by auto
  
  lemmas ADJUST_unfolds = ADJUST_PRE_SCOPE_unfolds ADJUST_PRE_PARAM_unfolds 
    ADJUST_POST_SCOPE_unfolds ADJUST_POST_PARAM_unfolds ADJUST_POST_RETV_unfolds
      
  (* TODO: Clean up these proofs! *)  
  lemma HT_mods_adjust_scope: 
    assumes "HT_mods \<pi> vs P c Q"
    shows "HT_mods \<pi> (Set.filter is_global vs) (ADJUST_PRE_SCOPE P) (SCOPE c) (ADJUST_POST_SCOPE Q)"
    using assms unfolding HT_mods_def 
    apply (drule_tac adjust_scope)
    apply simp
    apply (drule_tac HT_strengthen_modset)
    apply (erule HT_conseq)
     apply simp
    apply (clarsimp simp: modifies_split)
    apply (drule (1) modifies_join)
    apply (auto elim: modifies_mono[rotated])
    done
    
  lemma HT_mods_adjust_param: 
    assumes "HT_mods \<pi> vs P c Q"
    shows "HT_mods \<pi> (insert l vs) (ADJUST_PRE_PARAM l G P) (l[]::=G;; c) (ADJUST_POST_PARAM l G Q)"
    using assms unfolding HT_mods_def 
    apply (drule_tac adjust_assign_before[of \<pi> P c _ l G])
    apply (erule HT_conseq)
     apply simp
    apply (auto simp: modifies_def)
    done
    
  lemma HT_mods_adjust_retv:
    assumes "HT_mods \<pi> vs P c Q"
    shows "HT_mods \<pi> (insert G vs) P (c;; G[]::=l) (ADJUST_POST_RETV G l Q)"
    using assms unfolding HT_mods_def
    apply simp
    apply (unfold HT_def; clarsimp simp: wp_eq)
    apply (drule spec, erule (1) impE)
    apply (erule wp_conseq)
    apply (auto simp add: wp_eq modifies_def)
    by (metis fun_upd_triv)

  lemma HT_partial_mods_adjust_scope: 
    assumes "HT_partial_mods \<pi> vs P c Q"
    shows "HT_partial_mods \<pi> (Set.filter is_global vs) (ADJUST_PRE_SCOPE P) (SCOPE c) (ADJUST_POST_SCOPE Q)"
    using assms unfolding HT_partial_mods_def 
    apply (drule_tac adjust_scope_partial)
    apply (drule_tac HT_partial_strengthen_modset)
    apply (erule HT_partial_conseq)
     apply simp
    apply (clarsimp simp: modifies_split)
    apply (drule (1) modifies_join)
    apply (auto elim: modifies_mono[rotated])
    done
    
  lemma HT_partial_mods_adjust_param: 
    assumes "HT_partial_mods \<pi> vs P c Q"
    shows "HT_partial_mods \<pi> (insert l vs) (ADJUST_PRE_PARAM l G P) (l[]::=G;; c) (ADJUST_POST_PARAM l G Q)"
    using assms unfolding HT_partial_mods_def 
    apply (drule_tac adjust_assign_before_partial[of \<pi> P c _ l G])
    apply (erule HT_partial_conseq)
     apply simp
    apply (auto simp: modifies_def)
    done
    
  lemma HT_partial_mods_adjust_retv:
    assumes "HT_partial_mods \<pi> vs P c Q"
    shows "HT_partial_mods \<pi> (insert G vs) P (c;; G[]::=l) (ADJUST_POST_RETV G l Q)"
    using assms unfolding HT_partial_mods_def
    apply simp
    apply (unfold HT_partial_def; clarsimp simp: wlp_eq)
    apply (drule spec, erule (1) impE)
    apply (erule wlp_conseq)
    apply (auto simp add: wlp_eq modifies_def)
    by (metis fun_upd_triv)
    
        
end

lemma HT_generalize_penv:
  assumes "HT_mods Map.empty mods P c Q"
  shows "HT_mods \<pi> mods P c Q"
  using assms unfolding HT_mods_def HT_def wp_def
  apply auto 
  using big_step_mono_prog map_le_empty by blast

  
ML \<open>structure IMP2_Parameters 
  = struct
    fun adjust_retv_rl ctxt G l thm = let
      val G = HOLogic.mk_string G |> Thm.cterm_of ctxt
      val l = HOLogic.mk_string l |> Thm.cterm_of ctxt
      
      val rs_thms = @{thms HT_mods_adjust_retv HT_partial_mods_adjust_retv}
        |> map (Drule.infer_instantiate' ctxt [NONE, NONE, NONE, NONE, NONE, SOME G, SOME l])
    in thm RS_fst rs_thms end
  
    fun adjust_param_rl ctxt G l thm = let
      val G = HOLogic.mk_string G |> Thm.cterm_of ctxt
      val l = HOLogic.mk_string l |> Thm.cterm_of ctxt
      
      val rs_thms = @{thms HT_mods_adjust_param HT_partial_mods_adjust_param}
        |> map (Drule.infer_instantiate' ctxt [NONE, NONE, NONE, NONE, NONE, SOME l, SOME G])
    in thm RS_fst rs_thms end
    
    fun adjust_scope_rl (_:Proof.context) thm = thm RS_fst @{thms HT_mods_adjust_scope HT_partial_mods_adjust_scope}
      
    
    fun adjust_proc_rl imp_params imp_retvs ctxt thm = let
      val params = IMP_Syntax.zip_with_param_names imp_params
      val retvs = IMP_Syntax.zip_with_ret_names imp_retvs
      
      val ctxt = Named_Simpsets.put @{named_simpset vcg_bb} ctxt
      val ctxt = ctxt addsimps @{thms ADJUST_unfolds}
  
      val thm = thm
        |> fold_rev (uncurry (adjust_retv_rl ctxt)) retvs
        |> fold_rev (uncurry (adjust_param_rl ctxt)) params
        |> adjust_scope_rl ctxt
        |> Simplifier.simplify ctxt
    
    in
      thm
    end
  
  end
\<close>
  
  
  
subsubsection \<open>Recursion\<close>
lemma HT_mods_fold_call:
  assumes "\<pi> p = Some c"
  assumes "HT_mods \<pi> mods P c Q"
  shows "HT_mods \<pi> mods P (PCall p) Q"
  using assms 
  unfolding HT_mods_def HT_def
  by (auto simp: wp_eq wp_pcall_eq)

    
lemma localize_HT_mods: 
  assumes "HT_mods \<pi> mods P (PCall p) Q"
  shows "HT_mods \<pi>' mods P (PScope \<pi> (PCall p)) Q"
  using assms unfolding HT_mods_def HT_def wp_def
  by (simp add: localize_recursion)

lemmas localize_HT_mods' = localize_HT_mods[where \<pi>'="Map.empty"]
  

definition "PROVE_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 \<Theta> \<equiv> \<forall>P c Q. (f\<^sub>0,(P,c,Q))\<in>\<Theta> \<and> P s\<^sub>0 \<longrightarrow> wp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0"

lemma PROVE_\<Theta>I[vcg_preprocess_rules]:
  "PROVE_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 {}" 
  "\<lbrakk>\<lbrakk>RENAMING f\<^sub>0 f; BB_PROTECT (P s\<^sub>0)\<rbrakk> \<Longrightarrow> wp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0; PROVE_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 \<Theta>\<rbrakk> \<Longrightarrow> PROVE_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 (insert (f,(P,c,Q)) \<Theta>)" 
  unfolding PROVE_\<Theta>_def BB_PROTECT_def RENAMING_def
  by auto 

  
definition "JOIN_VARS f g P \<equiv> P f g"  
lemma JOIN_VARS: 
  "\<And>v f g P. JOIN_VARS (VAR v (\<lambda>x. f x)) g P = VAR v (\<lambda>x. JOIN_VARS (f x) g P)"
  "\<And>v f g P. JOIN_VARS f (VAR v (\<lambda>x. g x)) P = VAR v (\<lambda>x. JOIN_VARS f (g x) P)"
  "\<And>f g P. JOIN_VARS (BB_PROTECT f) (BB_PROTECT g) P = P f g"
  by (auto simp: JOIN_VARS_def BB_PROTECT_def VAR_def)
  
ML \<open>
  fun join_vars_rl ctxt thm0 = let 
    val thm = Local_Defs.unfold ctxt @{thms JOIN_VARS} thm0
    
    val t = Thm.prop_of thm
    val cns = Term.add_const_names t []
    val _ = member op= cns @{const_name JOIN_VARS} andalso raise THM("join_vars_rl: not joined",~1,[thm0,thm])
  in
    thm
  end
\<close>  
  
  
definition "ASSUME_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 R \<Theta> \<equiv> HT'set_r (\<lambda>f' s'. ((f' s'),(f\<^sub>0 s\<^sub>0))\<in>R ) \<pi> \<Theta>"
  
lemmas ASSUME_\<Theta>E1 = thin_rl[of "ASSUME_\<Theta> _ _ _ _ {}"]

lemma ASSUME_\<Theta>E2:
  assumes "ASSUME_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 R (insert (f,(P,c,Q)) \<Theta>)"
  obtains "HT' \<pi> (\<lambda>s. JOIN_VARS (f s) (P s) (\<lambda>v P. BB_PROTECT ((v,(f\<^sub>0 s\<^sub>0))\<in>R \<and> P))) c Q" "ASSUME_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 R \<Theta>"
  using assms unfolding ASSUME_\<Theta>_def HT'set_r_def JOIN_VARS_def BB_PROTECT_def by auto
  
lemmas ASSUME_\<Theta>E = ASSUME_\<Theta>E1 ASSUME_\<Theta>E2

lemma vcg_HT'setI:    
  assumes "wf R"
  assumes RL: "\<And>f\<^sub>0 s\<^sub>0. \<lbrakk> ASSUME_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 R \<Theta> \<rbrakk> \<Longrightarrow> PROVE_\<Theta> \<pi> f\<^sub>0 s\<^sub>0 \<Theta>"
  shows "HT'set \<pi> \<Theta>"
  using assms HT'setI[of R \<pi> \<Theta>] 
  unfolding ASSUME_\<Theta>_def PROVE_\<Theta>_def HT'set_def 
  by auto

  
subsubsection \<open>Consistency Check\<close>  

ML \<open>structure Spec_Consistency_Check 
  = struct
      fun check_ht_mods thm = let
        val (_,_,mods,P,_,Q) = Thm.concl_of thm 
          |> HOLogic.dest_Trueprop |> IMP2_Modified_Analysis.dest_HT_mods
      
        fun fail msg = raise THM ("Consistency check: "^msg,~1,[thm])
        
        (* Check that modset is OK *)  
        val _ = IMP2_Modified_Analysis.is_valid_modset mods orelse fail "invalid modset"
        
        (* Check for relicts in pre/postcondition *)
        val bad_consts = [
          @{const_name ADJUST_PRE_PARAM}, 
          @{const_name ADJUST_PRE_SCOPE}, 
          @{const_name ADJUST_POST_PARAM}, 
          @{const_name ADJUST_POST_RETV}, 
          @{const_name ADJUST_POST_SCOPE}
          ]

        fun is_bad_const (n,_) = member op= bad_consts n
          
        val _ = exists_Const is_bad_const P andalso fail "VCG relict in precondition"
        val _ = exists_Const is_bad_const Q andalso fail "VCG relict in precondition"
      in
        ()
      end
  
  end
\<close>
  
(* Summarizes postprocessors for specifications *)
ML \<open>structure Spec_Postprocessing 
  = struct
    (*
      Strip annotations
    *)
    fun cnv_HT'_to_HT ctxt = 
         IMP_Annotations.strip_annotations ctxt
      #> Local_Defs.unfold ctxt @{thms HT'_unfolds}
    
    (*
      Modifies Analysis
    *)
    val cnv_HT_to_HTmod = IMP2_Modified_Analysis.mk_HT_mods
      
    (*
      Make procedure frame
    *)
    val cnv_body_to_proc = IMP2_Parameters.adjust_proc_rl
    
    (*
      Generalize over procedure environment
    *)
    fun cnv_HTmod_generalize_penv thm = thm RS_fst @{thms HT_generalize_penv asm_rl}
  
    (*
      Define command as constant
    *)
    fun define_HTmod_const binding thm lthy = let
      (* Extract Command *)
      val (_,_,_,_,cmd,_) = Thm.concl_of thm |> HOLogic.dest_Trueprop |> IMP2_Modified_Analysis.dest_HT_mods

      (* Define *)
      val lhs = Free (Binding.name_of binding, fastype_of cmd)
      val eqn = Logic.mk_equals (lhs,cmd)
      val ((lhs,(_,def_thm)),lthy) = Specification.definition (SOME (binding,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,[]),eqn) lthy
      
      (* Fold definition in theorem *)
      val thm = Local_Defs.fold lthy [def_thm] thm
      
      (* Sanity check: Has definition actually been folded? *)
      val _ = exists_subterm (curry op = lhs) (Thm.prop_of thm)
        orelse raise THM("spec_program_cmd: Failed to fold command definition",~1,[thm])
      
    in
      ((binding,def_thm,thm), lthy)
    end 
    
    (*
      Declare defined command and specification to VCG
    *)
    fun declare_defined_spec (binding,def_thm,thm) lthy = let
      (* Sanity check: Various consistency checks *)  
      val _ = Spec_Consistency_Check.check_ht_mods thm

      val note = snd oo Local_Theory.note

      (* Note specification theorem, register as [vcg_rule] *)
      val spec_thm_name = Binding.suffix_name "_spec" binding
      val lthy = note ((spec_thm_name,@{attributes [vcg_specs]}),[thm]) lthy 
                
      (* Create lhsv-theorems, register as vcg_bb simp-rule *)
      val lhsv_thms = IMP2_Modified_Analysis.mk_lhsv_thms lthy def_thm
      val lhsv_thm_name = Binding.suffix_name "_lhsv" binding
      val lthy = note ((lhsv_thm_name,@{attributes [named_ss vcg_bb]}),lhsv_thms) lthy
    in
      lthy
    end

    fun define_declare binding thm = 
        define_HTmod_const binding thm 
      #> uncurry declare_defined_spec
        

  end
\<close>

subsection \<open>Program Specification Commands\<close>

ML \<open>structure Simple_Program_Specification 
  = struct
    fun simple_spec_program_cmd binding partial add_vars params pre_src post_src cmd_src lthy = let
      val total = not partial
      
      open IMP_Annotations
      
      val (prog_vars,prog_t) = IMP_Parser.parse_command_at lthy cmd_src
      
      val cfg = case params of 
        NONE => { add_vars = add_vars, in_vars=NONE, out_vars=NONE, prog_vars=prog_vars }
      | SOME (pvs,rvs) => { add_vars = add_vars, in_vars=SOME pvs, out_vars=SOME rvs, prog_vars=prog_vars }
      
      val prog_t = read_program cfg lthy prog_t
      
      val pre = gen_read_ta Syntax.read_term (mk_pre_reader cfg lthy) pre_src
      val post = gen_read_ta Syntax.read_term (mk_post_reader cfg lthy) post_src
      
      val goal = VCG_Htriple_Syntax.mk_htriple' total @{term "Map.empty::program"} (pre,prog_t,post)
      
      val goal = HOLogic.mk_Trueprop goal

      fun after_qed thmss lthy = let
      
        val param_post = case params of 
          NONE => K I 
        | SOME (pvs,rvs) => Spec_Postprocessing.cnv_body_to_proc pvs rvs
      
        val thm = flat thmss 
          |> the_single
          |> Spec_Postprocessing.cnv_HT'_to_HT lthy
          |> Spec_Postprocessing.cnv_HT_to_HTmod lthy
          |> param_post lthy
          |> Spec_Postprocessing.cnv_HTmod_generalize_penv

        val lthy = Spec_Postprocessing.define_declare binding thm lthy
      in
        lthy
      end
    
    in Proof.theorem NONE after_qed [[(goal,[])]] lthy end

  end
\<close>


ML \<open>structure Recursive_Program_Specification 
  = struct
      type proc_spec_src = {    
        binding:  binding,                   (* name *)
        params: string list,                 (* parameters *)
        retvs: string list,                  (* return variables *)
        addvars: IMP_Syntax.impvar list,     (* additional variables *)
        pre_src: string,                     (* precondition src *)
        post_src: string,                    (* postcondition src *)
        variant_src: string,                 (* variant src *)
        cmd_src: string * Position.T         (* body src *)
      }
  
      type proc_spec = {    
        binding:  binding,                   (* name *)
        params: string list,                 (* parameters *)
        retvs: string list,                  (* return variables *)
        addvars: IMP_Syntax.impvar list,     (* additional variables *)
        pre: term,                           (* precondition src *)
        post: term,                          (* postcondition src *)
        variant: term,                       (* variant src *)
        cmd: term                            (* body src *)
      }
      
          
      fun check_spec ctxt (spec_src : proc_spec_src) = let
        open IMP_Annotations
      
        val (prog_vars,prog_t) = IMP_Parser.parse_command_at ctxt (#cmd_src spec_src)
        val cfg = { 
          add_vars = #addvars spec_src, 
          in_vars=SOME (#params spec_src), 
          out_vars=SOME (#retvs spec_src), 
          prog_vars=prog_vars }
        
        val prog_t = read_program cfg ctxt prog_t
        
        val pre = gen_read_ta Syntax.read_term (mk_pre_reader cfg ctxt) (#pre_src spec_src)
        val post = gen_read_ta Syntax.read_term (mk_post_reader cfg ctxt) (#post_src spec_src)
        val variant = gen_read_ta Syntax.read_term (mk_variant_reader cfg ctxt) (#variant_src spec_src)
        
      in
        ({
          binding = (#binding spec_src),
          params=(#params spec_src),
          retvs=(#retvs spec_src),
          addvars=(#addvars spec_src),
          pre=pre,
          post=post,
          variant=variant,
          cmd=prog_t
        })
      end
  
  
      fun adjust_thm params retvs ctxt = let
        open Spec_Postprocessing
      in
        I
        #> cnv_HT'_to_HT ctxt
        #> cnv_HT_to_HTmod ctxt
        #> cnv_body_to_proc params retvs ctxt
      end
      
      fun gen_spec_program_cmd rel_src spec_srcs lthy = let
      
        val ctxt = lthy
      
        fun trace msg = tracing msg
      
        val _ = trace "(* Check Specification *)"
      
        val rel = the_default @{term \<open>measure nat\<close>} (Option.map (Syntax.read_term ctxt) rel_src)
        val relT = fastype_of rel |> HOLogic.dest_setT |> HOLogic.dest_prodT |> fst
      
        val specs = map (check_spec ctxt) spec_srcs
  
        val _ = trace "(* Create dummy procedure environment *)"
        (*val ctxt0 = ctxt*)
        val (pe_var,ctxt) = yield_singleton Proof_Context.add_fixes (@{binding \<pi>},SOME @{typ program},Mixfix.NoSyn) ctxt
        val pe_var = Free (pe_var,@{typ program})
        
        val _ = trace "(* Define initial goal *)"
        fun mk_theta_entry {variant, pre, cmd, post, ...} = HOLogic.mk_tuple [variant, HOLogic.mk_tuple [pre,cmd,post]]
        
        val thetaT = @{typ "'a \<Theta>elem_t"} |> typ_subst_atomic [(@{typ 'a},relT)]
        val theta = map mk_theta_entry specs |> HOLogic.mk_set thetaT
        
        val HT'setC = @{const HT'set ('a)} |> subst_atomic_types [(@{typ 'a},relT)]
        val goal = HT'setC $ pe_var $ theta
          |> HOLogic.mk_Trueprop
        
        val _ = trace "(* Start proof *)"
        val st = Thm.cterm_of ctxt goal |> Goal.init  
          
        val _ = trace "(* Apply recursion rule, and solve wf-precondition *)"
        val crel = Thm.cterm_of ctxt rel
        val sr_rl = Drule.infer_instantiate' ctxt [SOME crel] @{thm vcg_HT'setI}
  
        val st = Det_Goal_Refine.apply1 "" (resolve_tac ctxt [sr_rl]) st
        val st = Det_Goal_Refine.apply1 "Failed to solve wf-goal" 
          (SOLVED' (force_tac ctxt ORELSE' SELECT_GOAL (print_tac ctxt ""))) st
  
        val _ = trace "(* Explode theta-assumptions *)"
        val st = Det_Goal_Refine.apply1 "" (REPEAT_ALL_NEW (ematch_tac ctxt @{thms ASSUME_\<Theta>E})) st
      
        (* At this point, we have: \<And>f\<^sub>0 s\<^sub>0. \<lbrakk> HT' \<pi> \<dots>; HT' \<pi> \<dots>; \<dots> \<rbrakk> \<Longrightarrow> PROVE_\<Theta> \<pi> \<dots> *)
        
        val _ = trace "(* Join VARs in preconditions *)"
        val st = Det_Goal_Refine.apply1 "" (Thm_Mapping.map_all_prems_tac join_vars_rl ctxt) st
        
        val _ = trace "(* Wrap premises *)"
        fun wrap_thm_rl {params,retvs,...} ctxt thm = adjust_thm params retvs ctxt thm
        val wrap_thm_rls = map wrap_thm_rl specs 
        val st = Det_Goal_Refine.apply1 "" (Thm_Mapping.map_prems_tac wrap_thm_rls ctxt) st
        
        val _ = trace "(* Read wrapped commands to define procedure environment *)"
        val cmds = Logic.prems_of_goal (Thm.prop_of st) 1
          |> map (
               HOLogic.dest_Trueprop 
            #> IMP2_Modified_Analysis.dest_HT_mods
            #> #5
          )
          
        val _ = trace "(* Define procedure environment *)"
        fun proc_name_t_of {binding, ...} = HOLogic.mk_string (Binding.name_of binding)
          
        val penv_pairs = specs ~~ cmds
          |> map (apfst proc_name_t_of)
        
        val penv = HOLOption.mk_map_list @{typ pname} @{typ com} penv_pairs
                  
        val eqn = Logic.mk_equals (pe_var,penv) |> Thm.cterm_of ctxt
        val (pe_def,ctxt) = yield_singleton (Assumption.add_assms Local_Defs.def_export) eqn ctxt
  
        
        val _ = trace "(* Add theorem for lhsv\<pi> \<pi> *)"
        val lhsv_pi_thm = (@{lemma \<open>\<And>\<pi> \<pi>r. \<pi>\<equiv>\<pi>r \<Longrightarrow> lhsv\<pi> \<pi> = ANALYZE (lhsv\<pi> \<pi>r)\<close> by auto} OF [pe_def])
          |> vcg_bb_simplify [] ctxt
          
        val ctxt = Context.proof_map (Named_Simpsets.add_simp @{named_simpset vcg_bb} lhsv_pi_thm) ctxt
  
        val _ = trace "(* Finish modifies-analysis in HT' assumptions *)"
        fun finish_mdf ctxt thm = 
          (@{lemma \<open>\<And>\<pi> vs P c Q. HT_mods \<pi> vs P c Q \<Longrightarrow> HT_mods \<pi> (ANALYZE vs) P c Q\<close> by auto} OF [thm])
          |> vcg_bb_simplify [] ctxt
          
        val st = Det_Goal_Refine.apply1 "" (Thm_Mapping.map_all_prems_tac finish_mdf ctxt) st
        
        val _ = trace "(* Wrap assumptions into calls *)"
        (** First, show unfold theorems *)
        fun mk_unfold_thm (pname,com) = Goal.prove ctxt [] [] 
          (HOLogic.mk_eq (pe_var$pname,HOLOption.mk_Some com) |> HOLogic.mk_Trueprop)
          (fn {context=ctxt, ...} => ALLGOALS (vcg_bb_simp_tac [pe_def] ctxt))
        
        val unfold_thms = map mk_unfold_thm penv_pairs
                
        val wrap_call_rls = map (fn ufthm => fn _ => fn htthm => @{thm HT_mods_fold_call} OF [ufthm,htthm]) unfold_thms
        val st = Det_Goal_Refine.apply1 "" (Thm_Mapping.map_prems_tac wrap_call_rls ctxt) st
  
        val _ = trace "(* Focus on goal *)"
        val st_before_focus = st val ctxt_before_focus = ctxt
        val (focus as {context = ctxt, prems, ...},st) = Subgoal.focus ctxt 1 NONE st
        
        val _ = trace "(* Note ht-premises *)"
        val (_,ctxt) = Proof_Context.note_thms "" 
            ((Binding.name "rec_rules",[Named_Theorems.add @{named_theorems vcg_specs}]), 
              [(prems,[])]) ctxt
        
        val _ = trace "(* Prepare user proof *)"
        val termss = Thm.prems_of st |> map (fn t => (t,[]))
        
        (* --- user proof is logically here --- *)
        
        fun after_qed thmss goal_ctxt' = let
          val thms = flat thmss |> Proof_Context.export goal_ctxt' ctxt
          val _ = trace "(* Solve subgoals of st *)"
          val st = fold (fn thm => fn st => Thm.implies_elim st thm) thms st (* TODO: Use resolve_tac here? *)
           
          val st = singleton (Proof_Context.export ctxt (#context focus)) st
          
          val _ = trace "(* retrofit over focus, and finish goal *)"
          val st = Subgoal.retrofit (#context focus) ctxt_before_focus (#params focus) (#asms focus) 1 st st_before_focus 
            |> Det_Goal_Refine.seq_first ""
          val ctxt = ctxt_before_focus  
            
          val thm = Goal.finish ctxt st |> Goal.norm_result ctxt
          
          val _ = trace "(* Explode HT'set goal into single HTs *)"
          fun explode_HT'set thm = (case try (fn thm => thm RS @{thm HT'setD(1)}) thm of
            NONE => []
          | SOME thm' => thm' :: explode_HT'set (thm RS @{thm HT'setD(2)}))
  
          val thms = explode_HT'set thm
                  
          val _ = trace "(* Adjust theorems *)"
          
          val thms = thms
            |> Thm_Mapping.map_thms ctxt wrap_thm_rls
            |> Thm_Mapping.map_thms ctxt wrap_call_rls
          
          val thms = map (fn thm => thm RS @{thm localize_HT_mods}) thms  
  
          val _ = trace "(* Define constants *)"
          
          val ctxt = fold 
            (fn ({binding,...},thm) => Spec_Postprocessing.define_declare binding thm) 
            (specs ~~ thms) ctxt
            
        in
          ctxt
        end      
  
      in Proof.theorem NONE after_qed [termss] ctxt end
  end
\<close>


ML \<open> structure Program_Specification_Parser 
  = struct
    val parse_param_decls = Args.parens (Parse.enum "," Parse.name)
    
    val parse_var_decl = Parse.name -- Scan.optional (\<^keyword>\<open>[\<close>--\<^keyword>\<open>]\<close> >> K IMP_Syntax.ARRAY) IMP_Syntax.VAL
    val parse_var_decls = Scan.optional (\<^keyword>\<open>for\<close> |-- Scan.repeat parse_var_decl) []
  
    val parse_returns_clause = Scan.optional (
      \<^keyword>\<open>returns\<close> |-- (Args.parens (Parse.enum "," Parse.name) || Parse.name >> single)
    ) []
    
    val parse_proc_spec = (
          Parse.binding 
       -- parse_param_decls
       -- parse_returns_clause
      --| \<^keyword>\<open>assumes\<close> -- Parse.term 
      --| \<^keyword>\<open>ensures\<close> -- Parse.term 
      --| \<^keyword>\<open>variant\<close> -- Parse.term 
       -- parse_var_decls
      --| \<^keyword>\<open>defines\<close> -- (Parse.position (Parse.cartouche>>cartouche)) 
      ) >> (fn (((((((binding,params),retvs),pre_src),post_src),variant_src),addvars),cmd_src) => 
        {
          binding = binding, 
          params=params, 
          retvs=retvs, 
          pre_src=pre_src, 
          post_src=post_src, 
          variant_src=variant_src,
          addvars=addvars,
          cmd_src=cmd_src} : Recursive_Program_Specification.proc_spec_src
      )
    
    
  end
\<close>


  ML \<open>
    let
      open Simple_Program_Specification Recursive_Program_Specification Program_Specification_Parser
    in
      
      Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>program_spec\<close> "Define IMP program and prove specification"
        ((Args.mode "partial" -- Parse.binding 
          --| \<^keyword>\<open>assumes\<close> -- Parse.term 
          --| \<^keyword>\<open>ensures\<close> -- Parse.term 
           -- parse_var_decls
          --| \<^keyword>\<open>defines\<close> -- (Parse.position (Parse.cartouche>>cartouche)) 
          ) >> (fn (((((partial,bnd),pre_src),post_src),addvars),cmd_src) => 
                  simple_spec_program_cmd bnd partial addvars NONE pre_src post_src cmd_src));
    
    
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>procedure_spec\<close> "Define IMP procedure and prove specification"
      ((Args.mode "partial" -- Parse.binding 
         -- parse_param_decls
         -- parse_returns_clause
        --| \<^keyword>\<open>assumes\<close> -- Parse.term 
        --| \<^keyword>\<open>ensures\<close> -- Parse.term 
         -- parse_var_decls
        --| \<^keyword>\<open>defines\<close> -- (Parse.position (Parse.cartouche>>cartouche)) 
        ) >>
        
          (fn (((((((partial,bnd),params),retvs),pre_src),post_src),addvars),cmd_src) => 
                simple_spec_program_cmd bnd partial addvars (SOME (params,retvs)) pre_src post_src cmd_src
             )
         );
          
      Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>recursive_spec\<close> "Define IMP procedure and prove specification"
        (    Scan.option (\<^keyword>\<open>relation\<close> |-- Parse.term)
          -- Parse.and_list1 parse_proc_spec 
          >> (fn (rel,specs) => gen_spec_program_cmd rel specs))
        
    end
  \<close>

end
