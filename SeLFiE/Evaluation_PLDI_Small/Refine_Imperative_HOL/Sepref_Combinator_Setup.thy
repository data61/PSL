section \<open>Setup for Combinators\<close>
theory Sepref_Combinator_Setup
imports Sepref_Rules Sepref_Monadify
keywords "sepref_register" :: thy_decl
  and "sepref_decl_intf" :: thy_decl
begin

subsection \<open>Interface Types\<close>
text \<open>
  This tool allows the declaration of interface types.
  An interface type is a new type, and a rewriting rule to an existing (logic) type,
  which is used to encode objects of the interface type in the logic.
\<close>

context begin
  private definition T :: "string \<Rightarrow> unit list \<Rightarrow> unit" where "T _ _ \<equiv> ()"
  private lemma unit_eq: "(a::unit) \<equiv> b" by simp
  named_theorems "__itype_rewrite"

  ML \<open>
    signature SEPREF_INTF_TYPES = sig
      (* Declare new interface type *)
      val decl_intf_type_cmd: ((string list * binding) * mixfix) * string -> local_theory -> local_theory
      (* Register interface type rewrite rule *)
      val register_itype_rewrite: typ -> typ -> Proof.context -> local_theory

      (* Convert interface type to logical type*)
      val norm_intf_type: Proof.context -> typ -> typ

      (* Check whether interface type matches operation's type *)
      val check_intf_type: Proof.context -> typ -> typ -> bool
      (* Invoke msg with (normalized) non-matching types in case of no-match *)
      val check_intf_type_msg: (typ * typ -> unit) -> Proof.context -> typ -> typ -> unit
      (* Trigger error message if no match *)
      val check_intf_type_err: Proof.context -> typ -> typ -> unit

    end

    structure Sepref_Intf_Types: SEPREF_INTF_TYPES = struct
      fun t2t (Type(name,args)) = 
        @{term T}
          $HOLogic.mk_string name
          $HOLogic.mk_list @{typ unit} (map t2t args)
      | t2t (TFree (name,_)) = Var (("F"^name,0),HOLogic.unitT)
      | t2t (TVar ((name,i),_)) = Var (("V"^name,i),HOLogic.unitT)
  
      fun tt2 (t as (Var ((name,i),_))) = 
        if match_string "F*" name then TFree (unprefix "F" name, dummyS)
        else if match_string "V*" name then TVar ((unprefix "V" name,i), dummyS)
        else raise TERM("tt2: Invalid var",[t])
      | tt2 @{mpat "T ?name ?args"} = Type (HOLogic.dest_string name, HOLogic.dest_list args |> map tt2)
      | tt2 t = raise TERM("tt2: Invalid",[t])
  
      fun mk_t2t_rew ctxt T1 T2 = let
        fun chk_vars T = exists_subtype is_TVar T andalso raise TYPE("Type must not contain schematics",[T],[])
        val _ = chk_vars T1 
        val _ = chk_vars T2
  
        val free1 = Term.add_tfreesT T1 []
        val free2 = Term.add_tfreesT T2 []
  
        val _ = subset (=) (free2,free1) orelse raise TYPE("Free variables on RHS must also occur on LHS",[T1,T2],[])
  
      in
        Thm.instantiate' [] [
            t2t T1 |> Thm.cterm_of ctxt |> SOME,
            t2t T2 |> Thm.cterm_of ctxt |> SOME
          ] 
          @{thm unit_eq}
      end
  
      fun register_itype_rewrite T1 T2 lthy =
        lthy 
        |> Local_Theory.note ((Binding.empty,@{attributes ["__itype_rewrite"]}),[mk_t2t_rew lthy T1 T2])
        |> #2
  
      val decl_intf_type_parser = 
        Parse.type_args -- Parse.binding -- Parse.opt_mixfix --| @{keyword "is"} -- Parse.typ
  
      fun decl_intf_type_cmd (((args,a),mx),T2_raw) lthy = let
        val (T1,lthy) = Typedecl.typedecl {final = true} (a, map (rpair dummyS) args, mx) lthy
        val T2 = Syntax.read_typ lthy T2_raw
      in 
        register_itype_rewrite T1 T2 lthy
      end
  
      fun norm_intf_typet ctxt T = let
        val rew_rls = Named_Theorems.get ctxt @{named_theorems "__itype_rewrite"}
      in  
           t2t T 
        |> Thm.cterm_of ctxt 
        |> Drule.mk_term
        |> Local_Defs.unfold0 ctxt rew_rls
        |> Drule.dest_term
        |> Thm.term_of
      end
  
      fun norm_intf_type ctxt T = norm_intf_typet ctxt T |> tt2
  
      fun check_intf_type ctxt iT cT = let
        val it = norm_intf_typet ctxt iT
        val ct = t2t cT
        val thy = Proof_Context.theory_of ctxt
      in
        Pattern.matches thy (it,ct)
      end
  
      fun check_intf_type_msg msg ctxt iT cT = let
        val it = norm_intf_typet ctxt iT
        val ct = t2t cT
        val thy = Proof_Context.theory_of ctxt
      in
        if Pattern.matches thy (it,ct) then ()
        else msg (tt2 it, tt2 ct)
      end
  
      fun check_intf_type_err ctxt iT cT = let
        fun msg (iT',cT') = Pretty.block [
          Pretty.str "Interface type and logical type do not match",
          Pretty.fbrk,
          Pretty.str "Interface: ",Syntax.pretty_typ ctxt iT, Pretty.brk 1, 
          Pretty.str "  is   ", Syntax.pretty_typ ctxt iT', Pretty.fbrk,
          Pretty.str "Logical: ",Syntax.pretty_typ ctxt cT, Pretty.brk 1, 
          Pretty.str "  is   ", Syntax.pretty_typ ctxt cT', Pretty.fbrk
        ] |> Pretty.string_of |> error

      in
        check_intf_type_msg msg ctxt iT cT
      end

      val _ =
        Outer_Syntax.local_theory 
          @{command_keyword "sepref_decl_intf"} 
          "Declare interface type"
          ( decl_intf_type_parser >> decl_intf_type_cmd);
    end
  \<close>  

end


subsection \<open>Rewriting Inferred Interface Types\<close>
definition map_type_eq :: "'a itself \<Rightarrow> 'b itself \<Rightarrow> bool" 
  (infixr "\<rightarrow>\<^sub>n\<^sub>t" 60)
  where [simp]: "map_type_eq _ _ \<equiv> True"
lemma map_type_eqI: "map_type_eq L R" by auto

named_theorems_rev map_type_eqs

subsection \<open>ML-Code\<close>

context begin

private lemma start_eval: "x \<equiv> SP x" by auto
private lemma add_eval: "f x \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. f x)" by auto

private lemma init_mk_arity: "f \<equiv> id (SP f)" by simp
private lemma add_mk_arity: "id f \<equiv> (\<lambda>\<^sub>2x. id (f$x))" by auto
private lemma finish_mk_arity: "id f \<equiv> f" by simp

ML \<open>
  structure Sepref_Combinator_Setup = struct

    (* Check whether this term is a valid abstract operation *)
    fun is_valid_abs_op _ (Const _) = true
      | is_valid_abs_op ctxt (Free (name,_)) = Variable.is_fixed ctxt name
      | is_valid_abs_op _ @{mpat "PR_CONST _"} = true
      | is_valid_abs_op _ _ = false

    fun mk_itype ctxt t tyt = let
      val cert = Thm.cterm_of ctxt
      val t = cert t
      val tyt = cert tyt
    in
      Drule.infer_instantiate' ctxt [SOME t, SOME tyt] @{thm itypeI}
    end

    (* Generate mcomb-theorem, required for monadify transformation.
      t$x1$...$xn = x1\<leftarrow>EVAL x1; ...; xn\<leftarrow>EVAL xn; SP (t$x1$...$xn)
    *)
    fun mk_mcomb ctxt t n = let
      val T = fastype_of t
      val (argsT,_) = strip_type T
      val _ = length argsT >= n orelse raise TERM("Too few arguments",[t])
      val effT = take n argsT

      val orig_ctxt = ctxt
      val names = map (fn i => "x"^string_of_int i) (1 upto n)
      val (names,ctxt) = Variable.variant_fixes names ctxt
      val vars = map Free (names ~~ effT)

      val lhs = Autoref_Tagging.list_APP (t,vars)
        |> Thm.cterm_of ctxt
     
      fun add_EVAL x thm = 
        case Thm.prop_of thm of
          @{mpat "_ \<equiv> ?rhs"} => let
            val f = lambda x rhs |> Thm.cterm_of ctxt
            val x = Thm.cterm_of ctxt x
            val eval_thm = Drule.infer_instantiate' ctxt
              [SOME f, SOME x] @{thm add_eval}
            val thm = @{thm transitive} OF [thm,eval_thm]
          in thm end
        | _ => raise THM ("mk_mcomb internal: Expected lhs==rhs",~1,[thm])  

      val thm = Drule.infer_instantiate' ctxt [SOME lhs] @{thm start_eval}
      val thm = fold add_EVAL (rev vars) thm
      val thm = singleton (Proof_Context.export ctxt orig_ctxt) thm
    in
      thm
    end;

    (*
      Generate arity-theorem: t = \<lambda>x1...xn. SP t$x1$...$xn
    *)
    fun mk_arity ctxt t n = let
      val t = Thm.cterm_of ctxt t
      val thm = Drule.infer_instantiate' ctxt [SOME t] @{thm init_mk_arity}
      val add_mk_arity = Conv.fconv_rule (
        Refine_Util.ftop_conv (K (Conv.rewr_conv @{thm add_mk_arity})) ctxt)
      val thm = funpow n add_mk_arity thm
      val thm = Conv.fconv_rule (
        Refine_Util.ftop_conv (K (Conv.rewr_conv @{thm finish_mk_arity})) ctxt) thm
    in
      thm
    end;

    datatype opkind = PURE | COMB


    fun analyze_decl c tyt = let
      fun add_tcons_of (Type (name,args)) l = fold add_tcons_of args (name::l)
        | add_tcons_of _ l = l

      fun all_tcons_of P T = forall P (add_tcons_of T [])

      val T = Logic.dest_type tyt
      val (argsT,resT) = strip_type T

      val _ = forall (all_tcons_of (fn tn => tn <> @{type_name nres})) argsT 
        orelse raise TYPE (
          "Arguments contain nres-type "  
        ^ "(currently not supported by this attribute)",
        argsT,[c,tyt])

      val kind = case resT of  
        Type (@{type_name nres},_) => COMB
      | T => let
          val _ = all_tcons_of (fn tn => tn <> @{type_name nres}) T 
            orelse raise TYPE (
              "Result contains inner nres-type",
            argsT,[c,tyt])
        in
          PURE
        end

    in (kind,(argsT,resT)) end


    fun analyze_itype_thm thm = 
      case Thm.prop_of thm of
        @{mpat (typs) "Trueprop (intf_type ?c (_::?'v_T itself))"} => let
          val tyt = Logic.mk_type T
          val (kind,(argsT,resT)) = analyze_decl c tyt
        in (c,kind,(argsT,resT)) end
      | _ => raise THM("Invalid itype-theorem",~1,[thm]) 


    (*fun register_combinator itype_thm context = let
      val ctxt = Context.proof_of context
      val (t,kind,(argsT,_)) = analyze_itype_thm itype_thm
      val n = length argsT
    in  
      case kind of
        PURE => context
          |> Named_Theorems_Rev.add_thm @{named_theorems_rev id_rules} itype_thm
      | COMB => let    
          val arity_thm = mk_arity ctxt t n
          (*val skel_thm = mk_skel ctxt t n*)
          val mcomb_thm = mk_mcomb ctxt t n
        in
          context
          |> Named_Theorems_Rev.add_thm @{named_theorems_rev id_rules} itype_thm
          |> Named_Theorems_Rev.add_thm @{named_theorems_rev sepref_monadify_arity} arity_thm
          |> Named_Theorems_Rev.add_thm @{named_theorems_rev sepref_monadify_comb} mcomb_thm
          (*|> Named_Theorems_Rev.add_thm @{named_theorems_rev sepref_la_skel} skel_thm*)
        end
    end
    *)
    
    fun generate_basename ctxt t = let
      fun fail () = raise TERM ("Basename generation heuristics failed. Specify a basename.",[t])
      fun gb (Const (n,_)) = 
        (* TODO: There should be a cleaner way than handling this on string level!*)
        n |> space_explode "." |> List.last
        | gb (@{mpat "PR_CONST ?t"}) = gb t
        | gb (t as (_$_)) = let
            val h = head_of t
            val _ = is_Const h orelse is_Free h orelse fail ()
          in
            gb h
          end
        | gb (Free (n,_)) = 
            if Variable.is_fixed ctxt n then n 
            else fail ()
        | gb _ = fail ()    
    in
      gb t 
    end

    fun map_type_raw ctxt rls T = let
      val thy = Proof_Context.theory_of ctxt
  
      fun rewr_this (lhs,rhs) T = let
        val env = Sign.typ_match thy (lhs,T) Vartab.empty
      in 
        Envir.norm_type env rhs
      end
  
      fun map_Targs f (Type (name,args)) = Type (name,map f args)
        | map_Targs _ T = T
  
      fun 
        rewr_thiss (r::rls) T = 
          (SOME (rewr_this r T) handle Type.TYPE_MATCH => rewr_thiss rls T)
      | rewr_thiss [] _ = NONE
  
      fun 
        map_type_aux T = 
          let
            val T = map_Targs map_type_aux T
          in 
            case rewr_thiss rls T of
              SOME T => map_type_aux T
            | NONE => T  
          end
    in
      map_type_aux T
    end      

    fun get_nt_rule thm = case Thm.prop_of thm of
      @{mpat (typs) "Trueprop (map_type_eq (_::?'v_L itself) (_::?'v_R itself))"} =>
      let
        val Lvars = Term.add_tvar_namesT L []
        val Rvars = Term.add_tvar_namesT R []

        val _ = subset (=) (Rvars, Lvars) orelse (
          let
            val frees = subtract (=) Lvars Rvars
              |> map (Term.string_of_vname)
              |> Pretty.str_list "[" "]"
              |> Pretty.string_of
          in 
            raise THM ("Free variables on RHS: "^frees,~1,[thm])
          end)

      in
        (L,R)
      end

    | _ => raise THM("No map_type_eq theorem",~1,[thm])

    fun map_type ctxt T = let
      val rls = 
          Named_Theorems_Rev.get ctxt @{named_theorems_rev map_type_eqs}
       |> map get_nt_rule
    in map_type_raw ctxt rls T end  

    fun read_term_type ts tys lthy = case tys of
      SOME ty => let
        val ty = Syntax.read_typ lthy ty 
        val ctxt = Variable.declare_typ ty lthy
        val t = Syntax.read_term ctxt ts 
        val ctxt = Variable.declare_term t ctxt
      in
        ((t,ty),ctxt)
      end
    | NONE => let
        val t = Syntax.read_term lthy ts
        val ctxt = Variable.declare_term t lthy

        val tyt = fastype_of t |> map_type ctxt |> Logic.mk_type

        val tyt = tyt |> singleton (Variable.export_terms ctxt lthy)
        val (tyt,ctxt) = yield_singleton (Variable.import_terms true) tyt ctxt
        val ty = Logic.dest_type tyt
      in  
        ((t,ty),ctxt)
      end
  
    fun check_type_intf ctxt Tc Ti = let
      fun type2term (TFree (name,_)) = Var (("F"^name,0),HOLogic.unitT)
        | type2term (TVar ((name,i),_)) = Var (("V"^name,i),HOLogic.unitT)
        | type2term (Type (@{type_name "fun"},[T1,T2])) =
            Free ("F",HOLogic.unitT --> HOLogic.unitT --> HOLogic.unitT)
              $type2term T1$type2term T2
        | type2term (Type (name,argsT)) = let
            val args = map type2term argsT
            val n = length args
            val T = replicate n HOLogic.unitT ---> HOLogic.unitT
            val v = Var (("T"^name,0),T)
          in list_comb (v, args) end
    
      val c = type2term Tc
      val i = type2term Ti
      val thy = Proof_Context.theory_of ctxt
    in
      Pattern.matches thy (i,c)
    end

    (* Import all terms into context, with disjoint free variables *)
    fun import_terms_disj ts ctxt = let
      fun exp ctxt t = let 
        val new_ctxt = Variable.declare_term t ctxt
        val t = singleton (Variable.export_terms new_ctxt ctxt) t
      in t end
  
      val ts = map (exp ctxt) ts
  
      fun cons_fst f a (l,b) = let val (a,b) = f a b in (a::l,b) end
  
      val (ts,ctxt) = fold_rev (cons_fst (yield_singleton (Variable.import_terms true))) ts ([],ctxt)
    in
      (ts,ctxt)
    end
  
    type reg_thms = {
      itype_thm: thm,
      arity_thm: thm option,
      mcomb_thm: thm option
    }  

    fun cr_reg_thms t ty ctxt = let
      val orig_ctxt = ctxt
      val tyt = Logic.mk_type ty
      val ([t,tyt],ctxt) = import_terms_disj [t,tyt] ctxt

      val (kind,(argsT,_)) = analyze_decl t tyt
      val n = length argsT

      val _ = Sepref_Intf_Types.check_intf_type_err ctxt ty (fastype_of t)

      val _ = is_valid_abs_op ctxt t 
        orelse raise TERM("Malformed abstract operation. Use PR_CONST for complex terms.",[t])
      
      val itype_thm = mk_itype ctxt t tyt 
        |> singleton (Variable.export ctxt orig_ctxt)
    in
      case kind of
        PURE => {itype_thm = itype_thm, arity_thm = NONE, mcomb_thm = NONE}
      | COMB => let    
          val arity_thm = mk_arity ctxt t n 
            |> singleton (Variable.export ctxt orig_ctxt)
          val mcomb_thm = mk_mcomb ctxt t n
            |> singleton (Variable.export ctxt orig_ctxt)
        in    
          {itype_thm = itype_thm, arity_thm = SOME arity_thm, mcomb_thm = SOME mcomb_thm}
        end
    end

    fun gen_pr_const_pat ctxt t = 
      if is_valid_abs_op ctxt t then (NONE,t)
      else 
        let
          val ct = Thm.cterm_of ctxt t
          val thm = Drule.infer_instantiate' ctxt [SOME ct] @{thm UNPROTECT_def[symmetric]}
            |> Conv.fconv_rule (Conv.arg1_conv (Id_Op.protect_conv ctxt))
        in
          (SOME thm,@{mk_term "PR_CONST ?t"})
        end


    fun sepref_register_single basename t ty lthy = let
      fun mk_qualified basename q = Binding.qualify true basename (Binding.name q);
      fun 
        do_note _ _ NONE = I
      | do_note q attrs (SOME thm) = 
           Local_Theory.note ((mk_qualified basename q,attrs),[thm]) #> snd

      val (pat_thm,t) = gen_pr_const_pat lthy t

      val {itype_thm, arity_thm, mcomb_thm} = cr_reg_thms t ty lthy

      val lthy = lthy
          |> do_note "pat" @{attributes [def_pat_rules]} pat_thm
          |> do_note "itype" @{attributes [id_rules]} (SOME itype_thm)
          |> do_note "arity" @{attributes [sepref_monadify_arity]} arity_thm
          |> do_note "mcomb" @{attributes [sepref_monadify_comb]} mcomb_thm
      
    in
      (((arity_thm,mcomb_thm),itype_thm),lthy)
    end

    fun sepref_register_single_cmd ((basename,ts),tys) lthy = let
      val t = Syntax.read_term lthy ts
      val ty = map_option (Syntax.read_typ lthy) tys

      val ty = case ty of SOME ty => ty | NONE => fastype_of t |> map_type lthy

      val basename = case basename of
        NONE => generate_basename lthy t
        | SOME n => n
      
      val ((_,itype_thm),lthy) = sepref_register_single basename t ty lthy
      val _ = Thy_Output.pretty_thm lthy itype_thm |> Pretty.string_of |> writeln

    in
      lthy
    end

    val sepref_register_cmd = fold sepref_register_single_cmd

    val sepref_register_parser = Scan.repeat1 ( 
        Scan.option (Parse.name --| @{keyword ":"}) 
        -- Parse.term 
        -- Scan.option (@{keyword "::"} |-- Parse.typ)
      )

    val _ =
      Outer_Syntax.local_theory 
        @{command_keyword "sepref_register"} 
        "Register operation for sepref"
        ( sepref_register_parser
          >> sepref_register_cmd);

    val sepref_register_adhoc_parser = Scan.repeat1 (
      Args.term -- Scan.option (Scan.lift (Args.$$$ "::") |-- Args.typ)
    )

    fun sepref_register_adhoc_single (t,ty) context = let
      val ctxt = Context.proof_of context

      (* TODO: Map-type probably not clean, as it draws info from (current) context,
        which may have changed if registered elsewhere ...
      *)
      val ty = case ty of SOME ty => ty | NONE => fastype_of t |> map_type ctxt

      val (pat_thm,t) = gen_pr_const_pat ctxt t

      val {itype_thm, arity_thm, mcomb_thm} = cr_reg_thms t ty ctxt
      
      fun app _ NONE = I
        | app attr (SOME thm) = Thm.apply_attribute attr thm #> snd

    in
      context 
      |> app (Named_Theorems_Rev.add @{named_theorems_rev def_pat_rules}) pat_thm
      |> app (Named_Theorems_Rev.add @{named_theorems_rev id_rules}) (SOME itype_thm)
      |> app (Named_Theorems_Rev.add @{named_theorems_rev sepref_monadify_arity}) arity_thm
      |> app (Named_Theorems_Rev.add @{named_theorems_rev sepref_monadify_comb}) mcomb_thm
    end

    val sepref_register_adhoc = fold sepref_register_adhoc_single

    fun sepref_register_adhoc_attr ttys = Thm.declaration_attribute (K (sepref_register_adhoc ttys))

    val sepref_register_adhoc_attr_decl = sepref_register_adhoc_parser >> sepref_register_adhoc_attr

  end
\<close>

end

attribute_setup sepref_register_adhoc = Sepref_Combinator_Setup.sepref_register_adhoc_attr_decl
  \<open>Register operations in ad-hoc manner. Improper if this gets exported!\<close>

(*
attribute_setup sepref_register_combinator = 
  \<open>Scan.succeed (Thm.declaration_attribute Sepref_Combinator_Setup.register_combinator)\<close>
  \<open>Register combinator by its itype-rule. Set up itype,skel,arity, and mcomb rules.\<close>
*)

subsection \<open>Obsolete Manual Setup Rules\<close>

lemma 
      mk_mcomb1: "\<And>c. c$x1 \<equiv> (\<bind>)$(EVAL$x1)$(\<lambda>\<^sub>2x1. SP (c$x1))"
  and mk_mcomb2: "\<And>c. c$x1$x2 \<equiv> (\<bind>)$(EVAL$x1)$(\<lambda>\<^sub>2x1. (\<bind>)$(EVAL$x2)$(\<lambda>\<^sub>2x2. SP (c$x1$x2)))"
  and mk_mcomb3: "\<And>c. c$x1$x2$x3 \<equiv> (\<bind>)$(EVAL$x1)$(\<lambda>\<^sub>2x1. (\<bind>)$(EVAL$x2)$(\<lambda>\<^sub>2x2. (\<bind>)$(EVAL$x3)$(\<lambda>\<^sub>2x3. SP (c$x1$x2$x3))))"
    by auto

end
