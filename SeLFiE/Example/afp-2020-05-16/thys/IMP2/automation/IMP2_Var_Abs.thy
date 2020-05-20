section \<open>Abstraction over Program Variables\<close>
theory IMP2_Var_Abs
imports "../basic/Semantics" "../parser/Parser" IMP2_Basic_Simpset
begin
  
  definition VAR :: "'v \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'a" 
    where "VAR v f \<equiv> f v"
    
    
ML \<open> structure Program_Variables 
  = struct

    datatype T = AbsInfo of ((IMP_Syntax.impvar * string) * term) list * (string * term)
      (* (imp_var \<times> sfx_name \<times> Free) list \<times> (statename \<times> statev)
      
        where
          imp_var    -- IMP variable
          sfx_name   -- HOL variable name to bind to
          Free       -- Free variable in term that shall be abstracted
      
          statename  -- HOL variable name to bind state to
          statev     -- Free variable for state in term
        *)
  
    val stateN = "\<ss>"           (* Base name for state variable *)
    val nameT = @{typ vname}  (* HOL type of variable names *)
    val avalueT = @{typ val}    (* HOL type of array variable values *)
    val pvalueT = @{typ pval}    (* HOL type of primitive variable values *)

    
    fun mk_vref_t state_t (ivname,IMP_Syntax.VAL) = state_t $ IMP_Syntax.mk_varname ivname $ @{term "0::int"}
      | mk_vref_t state_t (ivname,IMP_Syntax.ARRAY) = state_t $ IMP_Syntax.mk_varname ivname
    
    val stateT = nameT --> avalueT
      
    fun abstract_var statev ((imp_var, sfx_name), v) t = let
      val T = fastype_of t
      val vT = fastype_of v
      val t = Term.lambda_name (sfx_name,v) t
      val vref_t = mk_vref_t statev imp_var
    in
      Const (@{const_name VAR}, vT --> (vT --> T) --> T) $ vref_t $ t
    end 
    
    fun get_statev (AbsInfo (_,(_,v))) = v
    
    (*
      Create context and abstraction info that binds imp variables to Isabelle 
      variable names. Moreover, the state is bound to Isabelle variable with name stateN and specified suffix.
    *)
    fun gen_declare_variables imp_x_isa_names isa_suffix ctxt = let
      val ctxt = ctxt |> Variable.set_body true

      val isa_statename = suffix isa_suffix stateN
      
      val (statev,ctxt) = yield_singleton Variable.add_fixes isa_statename ctxt
      val statev = Free (statev,stateT)
      val ctxt = Variable.declare_constraints statev ctxt
      
      fun imp_var_isa_T (_,IMP_Syntax.VAL) = pvalueT
        | imp_var_isa_T (_,IMP_Syntax.ARRAY) = avalueT
      
      fun declare_impv (imp_var,isa_name) ctxt = let
        val isa_name = suffix isa_suffix isa_name 
        
        val (vname,ctxt) = yield_singleton Variable.add_fixes isa_name ctxt
        val v = Free (vname, imp_var_isa_T imp_var)
        val ctxt = Variable.declare_constraints v ctxt
      in
        (((imp_var,isa_name),v), Proof_Context.augment v ctxt )
      end
      
      val (vs, ctxt) = fold_map declare_impv imp_x_isa_names ctxt
          
    in
      (AbsInfo (vs, (isa_statename, statev)), ctxt)
    end
    
    
    fun declare_variables imp_vars sfx ctxt = let
      val imp_x_isa_names = imp_vars ~~ (map fst imp_vars)
    in
      gen_declare_variables imp_x_isa_names sfx ctxt
    end  

    fun abstract_vars (AbsInfo (nsvs, (_,statev))) t = let
      val frees = Term.add_frees t [] |> map Free |> Termtab.make_set
      
      fun absv (nss,v) = 
        if Termtab.defined frees v then abstract_var statev (nss,v)
        else I
    
      val t = fold absv nsvs t
    in
      t
    end

    fun abstract_state (AbsInfo (_, (staten,statev))) t = Term.lambda_name (staten, statev) t

    fun abstract vinfo = abstract_vars vinfo #> abstract_state vinfo
      
  end
\<close>

end
