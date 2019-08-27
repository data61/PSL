section \<open>Parser\<close>
theory Parser
imports "../basic/Syntax"
begin

subsection \<open>Tagging\<close>
  text \<open>We define a few tag constants.
    They are inserted by the parser, and tag certain situations, 
    like parameter passing or inlined commands.
   \<close>
    
  definition Inline :: "com \<Rightarrow> com" where "Inline c = c"  
  
  definition Params :: "com \<Rightarrow> com" where "Params c \<equiv> c"

  text \<open>Assignment commands to assign the return value. 
    The VCG will add a renaming, such that the assigned variable name rather
    the \<open>G_ret\<close> will be used for the VCs\<close>
  definition "AssignIdx_retv x i rv \<equiv> AssignIdx x i (V rv)"      
  definition "ArrayCpy_retv x rv \<equiv> ArrayCpy x rv"      
    
  abbreviation "Assign_retv x rv \<equiv> AssignIdx_retv x (N 0) rv"

subsection \<open>Parser for IMP Programs\<close>

  text \<open>The parser also understands annotated programs.
    However, the basic parser will leave the annotations uninterpreted,
    and it's up to the client of the parser to interpret them.
  \<close>

  
  abbreviation (input) While_Annot :: "'a \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
    where "While_Annot I \<equiv> While"

  (* Note: Still a very early prototype *)

  abbreviation (input) VARIABLEI :: "string \<Rightarrow> string" where "VARIABLEI x \<equiv> x" (* Used to mark integer variables *)
  abbreviation (input) VARIABLEA :: "string \<Rightarrow> string" where "VARIABLEA x \<equiv> x" (* Used to mark array variables *)
  
  syntax "_annotated_term" :: "logic \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> logic" (* Annotated term: term string pos *)
  
  
  ML \<open>
    structure Term_Annot : sig
      (* Annotate terms *)
      val annotate_term: term -> string * Position.T -> term
      val dest_annotated_term: term -> (string * Position.T) * term
      
      (* Annotation = annotated dummy term *)
      val annotation: string * Position.T -> term
      val dest_annotation: term -> term

      (* Checking for annotations in Term *)
      val is_annotated_term: term -> bool
      val has_annotations: term -> bool

      (* Removing annotations *)
      val strip_annotations: term -> term
      (* Replaces annotated terms by dummy term *)
      val strip_annotated_terms: term -> term
            
      (* Parsing *)
      (* Parse cartouche (independent of term annotations)*)
      val parse_cartouche: (string * Position.T) parser
      (* Parse cartouche into annotation *)
      val parse_annotation: term parser
      (* Parse cartouche into annotation of syntax constant (used to get typed annotations) *)
      val parse_annotate: string -> term parser
      
      (* Read term from cartouche and position *)
      val read_term: Proof.context -> string * Position.T -> term
      
      (* Read annotation part of annotated term as term *)
      val read_annotation_as_term: Proof.context -> term -> term * term
    end = struct
      fun annotate_term t (str,pos) = let
        val pos = Free (Term_Position.encode pos,dummyT)
        val str = Free (str,dummyT)
        val c = Const (@{syntax_const "_annotated_term"}, dummyT --> dummyT --> dummyT --> dummyT)
      in
        c$t$str$pos
      end

      fun dest_annotated_term (Const (@{syntax_const "_annotated_term"},_)$t$Free (str,_)$Free (pos,_)) = let
            val pos = case Term_Position.decode pos of 
              SOME pos => pos | NONE => raise TERM ("dest_term_annot: invalid pos",[t])
          in ((str,pos),t) end
        | dest_annotated_term t = raise TERM("dest_annot",[t])      
        
      val is_annotated_term = can dest_annotated_term
      val has_annotations = Term.exists_subterm is_annotated_term

      val annotation = annotate_term Term.dummy
      val dest_annotation = dest_annotated_term #> #2
      
      val parse_cartouche = Parse.position Parse.cartouche >> apfst cartouche

      val parse_annotation = parse_cartouche >> annotation
      
      fun parse_annotate n = parse_cartouche >> annotate_term (Const (n,dummyT))
      
      fun read_term_tk ctxt tk = Args.term (Context.Proof ctxt, [tk]) |> #1
      
      fun read_term ctxt spos = let
        val tk = Symbol_Pos.explode spos |> Token.read_cartouche
      in
        read_term_tk ctxt tk
      end  
      
      fun read_annotation_as_term ctxt = dest_annotated_term #>> read_term ctxt 
      
      
      (* Strip one level of term annotations. *)
      fun strip_annotations (Const (@{syntax_const "_annotated_term"},_)$t$_$_) = t
        | strip_annotations (a$b) = strip_annotations a $ strip_annotations b
        | strip_annotations (Abs (x,T,t)) = Abs (x,T,strip_annotations t)
        | strip_annotations t = t

        
      fun strip_annotated_terms (Const (@{syntax_const "_annotated_term"},_)$_$_$_) = Term.dummy
        | strip_annotated_terms (a$b) = strip_annotated_terms a $ strip_annotated_terms b
        | strip_annotated_terms (Abs (x,T,t)) = Abs (x,T,strip_annotated_terms t)
        | strip_annotated_terms t = t
              
    end    
  \<close>
   
  
  ML \<open>
    structure IMP_Syntax = struct
    
      fun antf t = (
        exists_type is_TFree t andalso raise TERM("This won't support polymorphism in commands!",[t]);
        t)

      val mk_varname = HOLogic.mk_string 

      (*fun mk_aexp_V x = antf(@{term V})$x
      fun mk_aexp_Vidx x i = @{const Vidx}$x$i
      val mk_aexp_V' = mk_aexp_V o mk_var
      *)

      fun mk_aexp_const i = @{const N} $ HOLogic.mk_number @{typ int} i
                        
            
      fun mk_var_i x = Const (@{const_abbrev VARIABLEI}, dummyT) $ mk_varname x
      fun mk_var_a x = Const (@{const_abbrev VARIABLEA}, dummyT) $ mk_varname x


      (* Caution: This must match the Isabelle function is_global! *)
      fun is_global "" = true
        | is_global s = nth_string s 0 = "G"

      val is_local = not o is_global              
      
      (* Expressions *)

      datatype rval = RV_AEXP of term | RV_VAR of string
      fun rv_t (RV_AEXP t) = t
        | rv_t (RV_VAR x) = @{const Vidx} $ mk_var_i x $ mk_aexp_const 0

      val rv_var = RV_VAR
      fun rv_var_idx x i = RV_AEXP (@{const Vidx} $ mk_var_a x $ rv_t i)
      
      
      (*fun rv_int t = RV_AEXP (@{const N} $ (rv_t t))*)
      val rv_int' = RV_AEXP o mk_aexp_const

      fun rv_unop f t = RV_AEXP (f $ rv_t t)
      fun rv_binop f a b = RV_AEXP (f $ rv_t a $ rv_t b)
      
      fun rv_BC t = RV_AEXP (@{const Bc}$t)
      fun rv_BC' true = rv_BC @{const True}
        | rv_BC' false = rv_BC @{const False}

      fun rv_not t = RV_AEXP (@{const Not} $ rv_t t)
                      
      (* TODO: Add other constructors here *)
      
      (* TODO: Interface for variable tagging mk_var_xxx is not clear! *)
      
      (* Commands*)
      val mk_Skip = @{const SKIP}
      fun mk_Assign x t = antf(@{term Assign})$x$t
      fun mk_AssignIdx x i t = @{const AssignIdx}$x$i$t
      fun mk_ArrayCpy d s = @{const ArrayCpy}$d$s
      fun mk_ArrayInit d = @{const ArrayClear}$d
      fun mk_Scope c = @{const Scope}$c
      fun mk_Seq c1 c2 = @{const Seq}$c1$c2

      fun mk_Inline t = @{const Inline}$t
      fun mk_Params t = @{const Params}$t
        
      val While_Annot_c = Const (@{const_abbrev While_Annot}, dummyT --> @{typ "bexp \<Rightarrow> com \<Rightarrow> com"})
        
      fun mk_If b t e = @{const If} $ rv_t b $ t $ e
      fun mk_While_annot annots b c = While_Annot_c $ annots $ rv_t b $ c

      fun mk_pcall name = @{const PCall} $ (HOLogic.mk_string name)
      
              
      
      (* Derived Constructs *)

      datatype varkind = VAL | ARRAY
      type impvar = string * varkind      
      
      datatype lval = LV_IDX of string * term | LV_VAR of string

      fun lv_idx x rv = LV_IDX (x, rv_t rv)
      
                    
      fun mk_lr_assign (LV_IDX (x,i)) rv = mk_AssignIdx (mk_var_a x) i (rv_t rv)  
        | mk_lr_assign (LV_VAR x) (RV_AEXP e) = mk_Assign (mk_var_i x) e
        | mk_lr_assign (LV_VAR x) (RV_VAR v) = mk_ArrayCpy (mk_var_i x) (mk_var_i v)
        
      fun list_Seq [] = mk_Skip
        | list_Seq [c] = c
        | list_Seq (c::cs) = mk_Seq c (list_Seq cs)

        
      fun mk_AssignIdx_retv x i y = @{const AssignIdx_retv}$x$i$y
      fun mk_ArrayCpy_retv d s = @{const ArrayCpy_retv}$d$s
      fun mk_Assign_retv x t = antf(@{term Assign_retv})$x$t
      

      fun mk_assign_from_retv (LV_IDX (x,i)) y = mk_AssignIdx_retv (mk_var_a x) i (mk_var_i y)
        | mk_assign_from_retv (LV_VAR x) y = mk_ArrayCpy_retv (mk_var_i x) (mk_var_i y)
      
              
        
      fun param_varnames n = map (fn i => "G_par_"^Int.toString i) (1 upto n)
      fun zip_with_param_names xs = (param_varnames (length xs)) ~~ xs
      fun zip_with_param_lvs xs = map LV_VAR (param_varnames (length xs)) ~~ xs
      fun zip_with_param_rvs xs = map RV_VAR (param_varnames (length xs)) ~~ xs

      fun ret_varnames n = map (fn i => "G_ret_"^Int.toString i) (1 upto n)
      fun zip_with_ret_names xs = (ret_varnames (length xs)) ~~ xs
      fun zip_with_ret_lvs xs = map LV_VAR (ret_varnames (length xs)) ~~ xs
      fun zip_with_ret_rvs xs = map RV_VAR (ret_varnames (length xs)) ~~ xs

      fun mk_params ress name_t args = let
        val param_assigns = zip_with_param_lvs args
          |> map (uncurry mk_lr_assign)
      
        val res_assigns = zip_with_ret_names ress
          |> map (fn (rv,res) => mk_assign_from_retv res rv)  
          
        val res = param_assigns @ [mk_Params name_t] @ res_assigns  
          |> list_Seq
          
      in
        res
      end

      
    end  
  
  \<close>
  
    
   
  (* Syntax constants to discriminate annotation types *)
  syntax
    "_invariant_annotation" :: "_"
    "_variant_annotation" :: "_"
    "_relation_annotation" :: "_"
  
  
  ML \<open>
    structure IMP_Parser = struct
    
      fun scan_if_then_else scan1 scan2 scan3 xs = let
        val r = SOME (Scan.catch scan1 xs) handle Fail _ => NONE
      in
        case r of 
          NONE => scan3 xs
        | SOME (a,xs) => scan2 a xs
      end
      
    
      infixr 0 |||
      infix 5 ---
  
      fun (g,p) ||| e = scan_if_then_else g p e
          
      fun lastg (g,p) = g :|-- p
    
    
      datatype op_kind = Binop | Unop
      
      (*
      val int_c = @{const N}
      val bool_c = @{const Bc}
      val var_c = @{const V}
      *)
      
      
      type op_decl = op_kind * (string * term)

      fun name_eq_op_decl ((k,(a,_)), ((k',(b,_)))) = k=k' andalso a=b
      
      fun is_binop ((Binop,_):op_decl) = true | is_binop _ = false
      fun is_unop ((Unop,_):op_decl) = true | is_unop _ = false
      
      structure Opr_Data = Generic_Data (
        type T = op_decl list Inttab.table
        val empty = Inttab.empty
        val merge = Inttab.merge_list name_eq_op_decl
        val extend = I
      )
  
      fun tab_add_unop (p,n,f) = Inttab.insert_list name_eq_op_decl (p,(Unop,(n,f)))
      fun tab_add_binop (p,n,f) = Inttab.insert_list name_eq_op_decl (p,(Binop,(n,f)))
      
      val add_unop = Opr_Data.map o tab_add_unop
      val add_binop = Opr_Data.map o tab_add_binop

      val parse_varname = (Parse.short_ident || Parse.term_var) 
            
      
      local
        fun parse_level parse_opr op_decls = let
        
          open IMP_Syntax
        
          val binops = filter is_binop op_decls |> 
            map (fn (_,(k,c)) => Parse.$$$ k >> (K c))
          
          val unops = filter is_unop op_decls |>
            map (fn (_,(k,c)) => Parse.$$$ k >> (K c))
          
          val bopg = Parse.group (fn () => "Binary operator") (Scan.first binops) 
          val uopg = Parse.group (fn () => "Unary operator") (Scan.first unops) 
            
          
          fun mk_right a ([]) = a
            | mk_right a (((f,b)::fxs)) = mk_right (rv_binop f a b) fxs
          
          val parse_bop = (parse_opr, fn a => Scan.repeat (bopg -- parse_opr) >> mk_right a)
          val parse_unop = (uopg, fn f => parse_opr >> (fn x => rv_unop f x))
          
          val parse = (parse_bop ||| lastg parse_unop)
        in
          parse
        end
        
        fun parse_levels lvls = let
          open IMP_Syntax
        
          val parse_int = Parse.nat >> rv_int'
          val parse_var = parse_varname >> rv_var
          
          val pbc = Parse.keyword_markup (true,Markup.keyword3)
          
          val parse_bool = 
               pbc "true" >> (K (rv_BC' true))
            || pbc "false" >> (K (rv_BC' false))
        
          fun parse [] xs = (parse_int || parse_varidx || parse_var || parse_bool || (Parse.$$$ "(" |-- parse lvls --| Parse.$$$ ")")) xs
            | parse (lv::lvs) xs = (parse_level (parse lvs) lv) xs
          and parse_varidx xs = ((parse_varname -- Args.bracks (parse lvls)) 
            >> (fn (n,i) => rv_var_idx n i)) xs
            
        in
          parse lvls
        end
        
      in      
        val parse_exp_tab = Inttab.dest #> map snd #> parse_levels
        
        val parse_exp = Context.Proof #> Opr_Data.get #> parse_exp_tab
      end  

      (* TODO/FIXME: Going through the Args.term parser feels like a hack *)
      fun read_term_pos ctxt spos = Args.term (Context.Proof ctxt, [Token.make_string spos]) |> fst
      
      fun parse_proc_name ctxt = 
        Parse.$$$ "rec" |-- Parse.name >> IMP_Syntax.mk_pcall
        || Parse.name >> Syntax.read_term ctxt
        (*|| Parse.position Parse.name >> (read_term_pos ctxt)*)
      
      fun parse_args ctxt = Args.parens (Parse.enum "," (parse_exp ctxt))

      fun parse_lhs ctxt = 
         parse_varname -- Args.bracks (parse_exp ctxt) >> uncurry IMP_Syntax.lv_idx
      || parse_varname >> IMP_Syntax.LV_VAR     

      fun parse_multiret_lhs ctxt = 
        Args.parens (Parse.enum "," (parse_lhs ctxt))  
      
      fun parse_rhs_call ctxt = parse_proc_name ctxt -- parse_args ctxt
        

      fun g_parse_call_assign ctxt = 
        (parse_lhs ctxt --| Parse.$$$ "=", fn lhs => (parse_rhs_call ctxt >> (fn (f,args) => IMP_Syntax.mk_params [lhs] f args)
                           || (parse_exp ctxt >> (fn rhs => IMP_Syntax.mk_lr_assign lhs rhs))))
        
      fun g_parse_multiret_call ctxt = (
        (parse_multiret_lhs ctxt --| Parse.$$$ "=", fn ress => parse_rhs_call ctxt 
                                      >> (fn (f,args) => IMP_Syntax.mk_params ress f args)))
                                      
      fun g_parse_void_call ctxt = (parse_rhs_call ctxt, 
            fn (f,args) => Scan.succeed (IMP_Syntax.mk_params [] f args))
                          
      val fixed_keywords = ["(",")","{","}","true","false","[]","[","]",
        "if","else","while","scope","skip","=",";",",",
        "call", "sreturn", "inline","clear","rec",
        "@invariant", "@variant", "@relation",
        "__term"]
      
      fun parse_command ctxt = let
        val pkw = Parse.keyword_markup (true,Markup.keyword1)
        val pcm = Parse.keyword_markup (true,Markup.keyword2)
      
      
        val g_parse_skip = (pcm "skip", fn _ => Scan.succeed @{term SKIP})
        
        fun g_parse_block p = (Parse.$$$ "{", fn _ => p --| Parse.$$$ "}")

        val g_parse_clear = (pcm "clear", fn _ => parse_varname --| Parse.$$$ "[]" 
              >> (IMP_Syntax.mk_ArrayInit o IMP_Syntax.mk_var_a))
        
        
        val parse_invar_annotation = (pkw "@invariant", fn _ => Term_Annot.parse_annotate @{syntax_const "_invariant_annotation"})
        val parse_var_annotation = (pkw "@variant", fn _ => Term_Annot.parse_annotate @{syntax_const "_variant_annotation"})
        val parse_rel_annotation = (pkw "@relation", fn _ => Term_Annot.parse_annotate @{syntax_const "_relation_annotation"})

        val parse_while_annots = Scan.repeat (parse_invar_annotation ||| parse_var_annotation ||| lastg parse_rel_annotation)
              >> HOLogic.mk_tuple
        
        
        fun parse_atomic_com xs = 
          (
                g_parse_call_assign ctxt
            ||| g_parse_multiret_call ctxt
            ||| g_parse_void_call ctxt
            ||| g_parse_skip 
            ||| g_parse_clear
            ||| lastg (g_parse_block parse_com)
          ) xs
        
        and parse_com1 xs = (
            (pkw "if", fn _ => pkw "(" |-- parse_exp ctxt --| pkw ")" -- parse_com1 
              -- scan_if_then_else (pkw "else") (K parse_com1) (Scan.succeed IMP_Syntax.mk_Skip) 
                >> (fn ((b,t),e) => IMP_Syntax.mk_If b t e))
         ||| (pkw "while", fn _ => pkw "(" |-- parse_exp ctxt --| pkw ")" -- parse_while_annots -- parse_com1
                >> (fn ((b,annots),c) => IMP_Syntax.mk_While_annot annots b c))
         ||| (pkw "scope", fn _ => parse_com1 >> IMP_Syntax.mk_Scope)
         ||| (pkw "__term", fn _ => Term_Annot.parse_cartouche >> Term_Annot.read_term ctxt)
         ||| (pkw "inline", fn _ => Parse.position Parse.name >> (IMP_Syntax.mk_Inline o read_term_pos ctxt))
         ||| parse_atomic_com
        
        ) xs
        and parse_com xs = (
           parse_com1 -- (Scan.unless (Parse.$$$ ";") (Scan.succeed NONE) || Parse.$$$ ";" |-- parse_com >> SOME )
           >> (fn (s,SOME t) => IMP_Syntax.mk_Seq s t | (s,NONE) => s)
        
        ) xs
      
      in parse_com end 
      
      fun parse_all ctxt p src = let
        val src = map Token.init_assignable src
        val (res,_) = Scan.catch (Scan.finite Token.stopper (p --| Scan.ahead Parse.eof)) src
        
        val rp = map Token.reports_of_value src |> flat
        val _ = Context_Position.reports ctxt rp
        
        (* val src = map Token.closure src |> @{print} *)
      in
        res
      end
      
      val keywords_of_tab : op_decl list Inttab.table -> string list 
        = Inttab.dest_list #> map (snd#>snd#>fst)
      
      fun keywords ctxt = let 
        val kws = ctxt |> Context.Proof |> Opr_Data.get |> keywords_of_tab 
        val kws = (kws @ fixed_keywords)
          |> Symtab.make_set |> Symtab.keys
          |> map (fn x => ((x,Position.none),Keyword.no_spec))
      in
        Keyword.add_keywords kws Keyword.empty_keywords
      end
        
      fun parse_pos_text p ctxt (pos,text) = 
          Token.explode (keywords ctxt) pos text 
        |> filter Token.is_proper  
        |> parse_all ctxt (p ctxt)
        
      fun parse_sympos p ctxt xs = let
        val kws = keywords ctxt
        val tks = Token.tokenize kws {strict=true} xs
        val rp = map (Token.reports kws) tks |> flat  (* TODO: More detailed report AFTER parsing! *)
        val _ = Context_Position.reports_text ctxt rp
      in
          tks 
        |> filter Token.is_proper  
        |> parse_all ctxt (p ctxt)
      end

      fun variables_of t = let
        fun add (Const (@{const_abbrev VARIABLEI},_)$x) = (Symtab.default (HOLogic.dest_string x,IMP_Syntax.VAL))
          | add (Const (@{const_abbrev VARIABLEA},_)$x) = (Symtab.update (HOLogic.dest_string x,IMP_Syntax.ARRAY))
          | add (a$b) = add a #> add b
          | add (Abs (_,_,t)) = add t
          | add _ = I
      
      in
        add t Symtab.empty |> Symtab.dest
      end

      fun merge_variables vars = let
        fun add (x,IMP_Syntax.VAL) = Symtab.default (x,IMP_Syntax.VAL) 
          | add (x,IMP_Syntax.ARRAY) = Symtab.update (x,IMP_Syntax.ARRAY)
      in
        fold add vars Symtab.empty |> Symtab.dest
      end
      
      
      
      fun parse_command_at ctxt spos = let
        val syms = spos |> Symbol_Pos.explode |> Symbol_Pos.cartouche_content
        val res = parse_sympos parse_command ctxt syms
        val vars = variables_of res
      in
        (vars,res)
      end
    
      (* From Makarius: Protect a term such that it "survives" the subsequent translation phase *)
      fun mark_term (Const (c, T)) = Const (Lexicon.mark_const c, T)
        | mark_term (Free (x, T)) = Const (Lexicon.mark_fixed x, T)
        | mark_term (t $ u) = mark_term t $ mark_term u
        | mark_term (Abs (x, T, b)) = Abs (x, T, mark_term b)
        | mark_term a = a;
      
      
      fun cartouche_tr ctxt args = let  
        fun err () = raise TERM ("imp",args)
      
        fun parse spos = let 
          val (_,t) = parse_command_at ctxt spos 
          val t = if Term_Annot.has_annotations t then (warning "Stripped annotations from program"; Term_Annot.strip_annotated_terms t) else t
          val t = Syntax.check_term ctxt t
            |> mark_term
        in  
          t
        end
        
      in 
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ parse (s,pos) $ p
            | NONE => err ())
        | _ => err ())
      end
                
    end
  \<close>

  
  
  syntax "_Imp" :: "cartouche_position \<Rightarrow> logic" ("\<^imp>_")

  parse_translation \<open>
    [(@{syntax_const "_Imp"}, IMP_Parser.cartouche_tr)]
  \<close>

  term \<open>\<^imp>\<open>skip\<close>\<close>
  
  
  
    
  declaration \<open>K ( I
  #> IMP_Parser.add_unop (31,"-",@{term "Unop uminus"})  
  #> IMP_Parser.add_binop (25,"*",@{term "Binop (*)"})
  #> IMP_Parser.add_binop (25,"/",@{term "Binop (div)"})
  #> IMP_Parser.add_binop (25,"mod",@{term "Binop (mod)"})
  #> IMP_Parser.add_binop (21,"+",@{term "Binop (+)"})
  #> IMP_Parser.add_binop (21,"-",@{term "Binop (-)"})
  #> IMP_Parser.add_binop (11,"<",@{term "Cmpop (<)"})
  #> IMP_Parser.add_binop (11,"\<le>",@{term "Cmpop (\<le>)"})
  #> IMP_Parser.add_binop (11,">",@{term "Cmpop (>)"})
  #> IMP_Parser.add_binop (11,"\<ge>",@{term "Cmpop (\<ge>)"})
  #> IMP_Parser.add_binop (11,"==",@{term "Cmpop (=)"})
  #> IMP_Parser.add_binop (11,"\<noteq>",@{term "Cmpop (\<noteq>)"})
  #> IMP_Parser.add_unop (7,"\<not>",@{term "Not"})
  #> IMP_Parser.add_binop (5,"\<and>",@{term "BBinop (\<and>)"})
  #> IMP_Parser.add_binop (3,"\<or>",@{term "BBinop (\<or>)"})
    )\<close>

subsection \<open>Examples\<close>
    
experiment
begin

  definition \<open>p1 \<equiv> \<^imp>\<open> x = 42 \<close>\<close>

  ML_val \<open>Syntax.read_term @{context} "p1"\<close>
  
  term p1
  
  
  term \<open>\<^imp>\<open>
    x=y;                      \<comment> \<open>Variable assignment / array copy\<close>
    a[i] = x;                 \<comment> \<open>Assign array index\<close>
    clear a[];                \<comment> \<open>Array initialization\<close>
    
    
    a = b[i];                 \<comment> \<open>Array indexing\<close>
    b = a[1] + x*a[a[i]+1];   
        
    
    p1();                     \<comment> \<open>Function call, ignore return value\<close>
    
    p1(x,b+1,y[a]);           \<comment> \<open>Function call with parameters\<close>
    
    a[i]=p1();                \<comment> \<open>Return value assigned to \<open>a[i]\<close>\<close>  
    a=p1();                   \<comment> \<open>Returns array (also works for value)\<close>
    
    (a,b,c) = p1(a,b);        \<comment> \<open>Multiple return values\<close>
    
    
    \<comment> \<open>Special syntax for recursive calls. TODO: Get rid of this? \<close>
    rec p();
    rec p(a,b);
    a = rec p(a,b);
    (a,b,c) = rec p(a,b);
    
    skip
  \<close>\<close>
  
  
  term  \<open> \<^imp>\<open>
    a = 1;
    if (true) a=a;
    if (false) skip else {skip; skip};
    while (n > 0) 
      @invariant \<open>not interpreted here\<close>
      @variant \<open>not interpreted here\<close>
      @relation \<open>not interpreted here\<close>
    {
      a = a + a;
      
      __term \<open>SKIP;; p1\<close>;
      
      inline p1;
      
      y = p1();
      scope {
        n=0
      };
      
      n = n - 1
    }
  \<close>\<close>  
   
end  

term "\<^imp>\<open>
    a=1;
    while (n>0) {
      a=a+a;
      n=n-1
    }
  \<close>"

subsubsection \<open>Parameter Passing\<close>  

experiment
begin
  text \<open>The parser generates parameter and return value passing code, using the global
    variables \<open>G_par_i\<close> and \<open>G_ret_i\<close>. 

    To illustrate this, we first define an example procedure. Its signature would be
      \<open>(int,int) f (int p1, int p2)\<close>
    
  \<close>
  definition "f \<equiv> \<^imp>\<open>scope { p1 = G_par_1; p2 = G_par_2; G_ret_1=x1+x2; G_ret_2=x1-x2 }\<close>"

  text \<open>The parser generates the corresponding caller-side code for the invocation of 
    this procedure:\<close>
  term \<open>\<^imp>\<open>(x1,x2) = f(a,b+1)\<close>\<close>


end

end
