open Derive_Util

signature DERIVE =
sig
  (* Adds functions that convert to and from a product-sum representation *)
  val define_prod_sum_conv : type_info -> bool -> Proof.context -> (Function_Common.info * Function_Common.info * Proof.context)
  (* define product-sum-representation type synonym *)
  val define_rep_type : string list -> ctr_info -> bool -> local_theory -> rep_type_info * local_theory
  (* define Mu-combinator type *)
  val define_combinator_type : string list -> (typ * class list) list -> rep_type_info 
                                -> local_theory -> comb_type_info option * local_theory
  (* instantiate a typeclass *)
  val generate_instance : string -> sort -> bool -> theory -> Proof.state

  val add_inst_info : string -> string -> thm list -> theory -> theory
end

structure Derive : DERIVE =
struct      

fun get_type_info thy tname constr_names = Symtab.lookup (Type_Data.get thy) (mk_key tname constr_names)
fun get_class_info thy classname = Symtab.lookup (Class_Data.get thy) classname
fun get_inst_info thy classname tname = Symtab.lookup (Instance_Data.get thy) (hash_string (classname ^ tname))
fun add_params_cl_info (cl_info : class_info) params = 
  {classname = (#classname cl_info), class = (#class cl_info), params = SOME params, class_law = (#class_law cl_info), class_law_const = (#class_law_const cl_info), ops = (#ops cl_info), transfer_law = (#transfer_law cl_info), axioms = (#axioms cl_info), axioms_def = (#axioms_def cl_info), class_def = (#class_def cl_info), equivalence_thm = (#equivalence_thm cl_info)}
fun mk_inst_info defs = 
  {defs = defs}
fun add_equivalence_cl_info (cl_info : class_info) equivalence_thm = 
  {classname = (#classname cl_info), class = (#class cl_info), params = (#params cl_info), class_law = (#class_law cl_info), class_law_const = (#class_law_const cl_info), ops = (#ops cl_info), transfer_law = (#transfer_law cl_info), axioms = (#axioms cl_info), axioms_def = (#axioms_def cl_info), class_def = (#class_def cl_info), equivalence_thm = SOME equivalence_thm}

fun make_rep T lthy conv_func (btype,bname) = 
  let 
  val term = 
    case btype of
      (TFree _) => conv_func $ (Free (bname, T)) |
      (Type (_, _)) => if is_polymorphic btype then (get_mapping_function lthy btype) $ conv_func $ (Free (bname, dummyT))
                                              else Free (bname, btype) |
       _ => Free (bname, btype)
  in hd (Type_Infer_Context.infer_types lthy [term]) 
  end

fun from_rep T lthy conv_func inner_term = 
  let 
  val term = 
    case T of
      (TFree _) => conv_func $ inner_term |
      (Type (_, _)) => if is_polymorphic T then (get_mapping_function lthy T) $ conv_func $ inner_term
                                           else inner_term |
       _ => inner_term
  in hd (Type_Infer_Context.infer_types lthy [term]) 
  end

(* Generate instance for Mu-combinator type *)
fun instantiate_combinator_type (ty_info : type_info) (cl_info : class_info) constr_names lthy = 
  let
    val tname = #tname ty_info
    val ctr_type =  #rep_type_instantiated (the (#comb_info ty_info))
    val rep_type = #rep_type (#rep_info ty_info)
    val comb_type_name = #combname (the (#comb_info ty_info))
    val comb_type_name_full = #combname_full (the (#comb_info ty_info))
    val class = #class cl_info
    val params = the (#params cl_info)

    val sum_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.sum\<close> else \<^type_name>\<open>Sum_Type.sum\<close>
    val prod_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.prod\<close> else \<^type_name>\<open>Product_Type.prod\<close>

    val _ = ("Generating instance for type " ^ quote comb_type_name) |> writeln

    fun define_modular_sum_prod def vars opname opT opT_var is_sum lthy = 
      let
        fun get_tvars vars =
          if null vars 
            then ((TVar (("'a",0),class)),(TVar (("'b",0),class)))
            else 
              let 
                val var = hd vars
                val varTname = if is_typeT var then var |> dest_Type |> fst else ""
              in
                if is_sum then 
                  (if varTname = sum_type_name 
                    then var |> dest_Type |> snd |> (fn Ts => (hd Ts, hd (tl Ts))) 
                    else get_tvars ((var |> dest_Type |> snd)@(tl vars)))
                else
                  (if varTname = prod_type_name 
                    then var |> dest_Type |> snd |> (fn Ts => (hd Ts, hd (tl Ts))) 
                    else get_tvars ((var |> dest_Type |> snd)@(tl vars)))
              end
        fun replace_tfree tfree replacement T = 
          if T = tfree then replacement else T
        fun replace_op_call opname T replacement t =
          if t = Const (opname,T) then replacement else t
        fun is_TFree (TFree _) = true | is_TFree _ = false
        fun remove_constraints T = if is_TFree T then dest_TFree T |> apsnd (K \<^sort>\<open>type\<close>) |> TFree else T
        val varTs = map (dest_Var #> snd) vars
        val (left,right) = get_tvars (varTs @ [strip_type opT_var |> snd])
        val op_tfree = Term.add_tfreesT opT [] |> hd |> TFree
        val left_opT = map_atyps (replace_tfree op_tfree left) opT
        val right_opT = map_atyps (replace_tfree op_tfree right) opT
        val opname_left = (Long_Name.base_name opname) ^ "_left"
        val opname_right = (Long_Name.base_name opname) ^ "_right"
        val var_left = (Var ((opname_left,0),left_opT))
        val var_right = (Var ((opname_right,0),right_opT))
        val def_left = map_aterms (replace_op_call opname left_opT var_left) def
        val def_right = map_aterms (replace_op_call opname right_opT var_right) def_left
        val return_type = strip_type opT_var |> snd 
        val def_name = (Long_Name.base_name opname) ^ (if is_sum then "_sum_modular" else "_prod_modular")
        val eq_head = Free (def_name, ([left_opT,right_opT]@varTs) ---> return_type)
          |> Logic.unvarify_types_global
        val args = map Logic.unvarify_global ([var_left,var_right] @ vars)
        val eq = HOLogic.Trueprop $ 
          HOLogic.mk_eq ((list_comb (eq_head,args)), Logic.unvarify_global def_right)
        val eq' = map_types (map_atyps remove_constraints) eq

        val ((_,(_,def_thm)),lthy') = Specification.definition NONE [] [] ((Binding.empty, []), eq') lthy

        val left = left |> dest_TVar |> (fn ((s,_),_) => TFree (s,\<^sort>\<open>type\<close>))
        val right = right |> dest_TVar |> (fn ((s,_),_) => TFree (s,\<^sort>\<open>type\<close>))
        val def_const = Thm.hyps_of def_thm |> hd |> Logic.dest_equals |> snd
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy')
        val def_thm = singleton (Proof_Context.export lthy' ctxt_thy) def_thm
      in
        (left,right,def_const,def_thm,lthy')
      end

    fun op_instance opname opT T =
      let
        fun replace_tfree tfree replacement T = 
          if T = tfree then replacement else T
        val op_tfree = Term.add_tfreesT opT [] |> hd |> TFree
        val opT_new = map_atyps (replace_tfree op_tfree T) opT
      in
        Const (opname,opT_new)
      end

    fun sum_prod_instance term lvar rvar lT rT =
      let
        fun replace_vars var1 var2 replacement1 replacement2 T =
          if T = var1 then replacement1 else if T = var2 then replacement2 else T
      in
        map_types (map_atyps (replace_vars lvar rvar lT rT)) term
      end

    fun define_modular_instance T (lvs,rvs,sum_term) (lvp,rvp,prod_term) opname opT =
      if is_typeT T 
        then 
          let
            val (tname,Ts) = dest_Type T
          in
            if tname = sum_type_name 
              then (sum_prod_instance sum_term lvs rvs (hd Ts) (hd (tl Ts))) 
                 $ (define_modular_instance (hd Ts) (lvs,rvs,sum_term) (lvp,rvp,prod_term) opname opT)
                 $ (define_modular_instance (hd (tl Ts)) (lvs,rvs,sum_term) (lvp,rvp,prod_term) opname opT)
            else if tname = prod_type_name 
              then (sum_prod_instance prod_term lvp rvp (hd Ts) (hd (tl Ts)))
                 $ (define_modular_instance (hd Ts) (lvs,rvs,sum_term) (lvp,rvp,prod_term) opname opT)
                 $ (define_modular_instance (hd (tl Ts)) (lvs,rvs,sum_term) (lvp,rvp,prod_term) opname opT)
            else (op_instance opname opT T)
          end
        else (op_instance opname opT T)
    
    fun change_constraints constrT term =
      let
        val constraint = Term.add_tfreesT constrT [] |> hd |> snd
        val unconstr_tfrees = Term.add_tfrees term [] |> map TFree
        val constr_names = Name.invent_names (Variable.names_of lthy) "a" (replicate (length unconstr_tfrees) constraint)
        val constr_tfrees = map TFree constr_names
      in
        subst_atomic_types (unconstr_tfrees ~~ constr_tfrees) term
      end

    fun define_operation_rec T (opname,t) lthy =
      let    
        fun get_comb_params [] = [] |
            get_comb_params (ty::tys) =
              (case ty of Type (n,tys') => if n = comb_type_name_full then tys' else get_comb_params (tys@tys') |
                          _ => get_comb_params tys)
        fun make_arg inConst ctr_type x =
          let
            val T = dest_Free x |> snd
          in 
            if T = ctr_type then inConst $ x else (x |> dest_Free |> apsnd (K dummyT) |> Free) 
          end

        val short_opname = Long_Name.base_name opname
        val fun_name = short_opname ^ "_" ^ comb_type_name
        val prod_def_name = short_opname ^ "_prod_def"
        val prod_thm = Proof_Context.get_thm lthy prod_def_name
        val prod_hd = (Thm.full_prop_of prod_thm) |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst  
        val prod_const = prod_hd |> combs_to_list |> hd
        val prod_opT = prod_const |> dest_Const |> snd
        val prod_vars_raw = prod_hd |> combs_to_list |> tl
        val prod_def = (Thm.full_prop_of prod_thm) |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
        val (lvp,rvp,prod_def_term,prod_def_thm,lthy') = define_modular_sum_prod prod_def prod_vars_raw opname t prod_opT false lthy

        val sum_def_name = short_opname ^ "_sum_def"
        val sum_thm = Proof_Context.get_thm lthy sum_def_name
        val sum_hd = (Thm.full_prop_of sum_thm) |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
        val sum_const = sum_hd |> combs_to_list |> hd
        val sum_opT = sum_const |> dest_Const |> snd
        val sum_vars_raw = sum_hd |> combs_to_list |> tl
        val sum_def = (Thm.full_prop_of sum_thm) |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
        val (lvs,rvs,sum_def_term,sum_def_thm,lthy'')  = define_modular_sum_prod sum_def sum_vars_raw opname t sum_opT true lthy'
        
        val (binders, body) = (strip_type t)
        val tvar = get_tvar (body :: binders)
        val comb_params = get_comb_params [ctr_type]
        val T_params = dest_Type T |> snd
        val ctr_type' = typ_subst_atomic (comb_params ~~ T_params) ctr_type 
        val body' = typ_subst_atomic [(tvar,dummyT)] body
        val binders' = map (typ_subst_atomic [(tvar,ctr_type')]) binders
        val opT = (replicate (length binders) dummyT) ---> body'
        val vars = (Name.invent_names (Variable.names_of lthy) "x" binders')
        val xs = map Free vars
        val inConst_name = Long_Name.qualify comb_type_name_full "In"
        val inConst = Const (inConst_name, ctr_type' --> dummyT)
        val xs_lhs = map (make_arg inConst ctr_type') xs

        val modular_instance = define_modular_instance rep_type (lvs,rvs,sum_def_term) (lvp,rvp,prod_def_term) opname t
        val xs_modular = map (apsnd (K dummyT) #> Free) vars
        val modular_folded_name = short_opname ^ "_modular_folded"
        val modularT = typ_subst_atomic [(tvar,rep_type)] t
        val modular_instance_eq = HOLogic.Trueprop $ HOLogic.mk_eq (Free (modular_folded_name, modularT),modular_instance)
        val modular_eq_constr = change_constraints t modular_instance_eq
        val ((_,(_,modular_folded_thm)),lthy''') = Specification.definition NONE [] [] ((Binding.empty, []), modular_eq_constr) lthy''

        val modular_unfolded = Local_Defs.unfold lthy''' [prod_def_thm,sum_def_thm] modular_folded_thm
                                 |> Thm.full_prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd |> map_types (K dummyT)

        val lhs = list_comb (Free (fun_name, opT), xs_lhs)
        val rhs = if is_polymorphic body 
                    then inConst $ list_comb (modular_unfolded,xs_modular) 
                    else list_comb (modular_unfolded,xs_modular)
        val eq = HOLogic.Trueprop $ HOLogic.mk_eq (lhs, rhs)
      in 
        if xs = [] then 
          Specification.definition NONE [] [] ((Binding.empty, []), eq) lthy |> snd
        else 
          if constr_names then
             Function.add_function
               [(Binding.name fun_name, NONE, NoSyn)]
               [((Binding.empty_atts, eq), [], [])]
               Function_Fun.fun_config 
               (fn ctxt => Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt)
               lthy 
             |> snd
             |> tagged_function_termination_tac
             |> snd
           else
             Function_Fun.add_fun 
               [(Binding.name fun_name, NONE, NoSyn)]
               [((Binding.empty_atts, eq), [], [])]
               Function_Fun.fun_config lthy
    end
      
    fun instantiate_comb_type lthy =
      let
        val thy = Named_Target.exit lthy
        val (T,xs) = Derive_Util.typ_and_vs_of_typname thy comb_type_name_full class
        val filtered_params = 
          filter (fn (c,_) => 
            (not (is_instantiated thy comb_type_name_full c)) andalso not (is_instantiated thy tname c))
            params
        fun  
          define_operations_rec_aux _ [] lthy = lthy |
          define_operations_rec_aux ty (p::ps) lthy = define_operations_rec_aux ty ps (define_operation_rec ty p lthy)
      in
        Class.instantiation ([comb_type_name_full], xs, class) thy
        |> (define_operations_rec_aux T (map snd filtered_params)) 
      end
      
    in
    instantiate_comb_type lthy
  end

fun define_operation lthy tname T (opname,t) =
  let
    val from_name = "from_" ^ Long_Name.base_name tname
    val from_term = (Proof_Context.read_const {proper = true, strict = true} lthy from_name) 
                      |> dest_Const |> fst
    val from_func = Const (from_term, dummyT)
    val to_name = "to_" ^ Long_Name.base_name tname
    val to_term = (Proof_Context.read_const {proper = true, strict = true} lthy to_name) 
                      |> dest_Const |> fst
    val to_func = Const (to_term, dummyT)
    val (binders, body) = (strip_type t)
    val tvar = get_tvar (body :: binders)
    val body' = typ_subst_atomic [(tvar,dummyT)] body
    val binders' = map (typ_subst_atomic [(tvar,T)]) binders
    val newT = binders' ---> body'
    val vars = (Name.invent_names (Variable.names_of lthy) "x" binders')
    val names = map fst vars
    val xs = map Free vars
    val lhs = list_comb (Const (opname, newT), xs)
    val rhs_inner = list_comb (Const (opname, dummyT), map (make_rep T lthy from_func) (binders ~~ names))
    val rhs = from_rep body lthy to_func rhs_inner
    val eq = HOLogic.Trueprop $ HOLogic.mk_eq (lhs, rhs)
    val ((_,(_,thm)),lthy') = (Specification.definition NONE [] [] ((Binding.empty, []), eq) lthy)
  in 
    (thm,lthy')
end

fun define_operations ps ty lthy =
let 
  fun 
    define_operations_aux [] _ thms lthy = (thms,lthy) |
    define_operations_aux (p::ps) (tname,T) thms lthy =  
      if not (is_instantiated (Proof_Context.theory_of lthy) tname (fst p))
      then 
        let  
          val (thm,lthy') = define_operation lthy tname T (snd p) 
        in define_operations_aux ps (tname,T) (thm :: thms) lthy'
        end
      else
        let
          val params = #defs (the_default {defs=[]} (get_inst_info (Proof_Context.theory_of lthy) (fst p) tname))
          val names = map (Thm.full_prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst #> strip_comb #> fst #> dest_Const #> fst) params
          val thm = the (AList.lookup (op =) (names ~~ params) (fst (snd p)))
        in define_operations_aux ps (tname,T) (thm :: thms) lthy
        end
in
  define_operations_aux ps ty [] lthy
end

fun abstract_over_vars vars t =
          let
            val varnames = map dest_Free vars |> map fst
            val varmapping = varnames ~~ (List.tabulate (length vars, I))
            val increment_bounds = map (fn (v,n) => (v,n + 1))
            fun 
              insert_bounds varmapping (Free (s,T)) = 
                (case AList.lookup (op =) varmapping s of
                  NONE => Free (s,T) |
                  SOME i => Bound i) | 
              insert_bounds varmapping (Abs (x,T,t)) = Abs (x,T,insert_bounds (increment_bounds varmapping) t) |
              insert_bounds varmapping (s $ t) = (insert_bounds varmapping s) $ (insert_bounds varmapping t) |
              insert_bounds _ t = t
            fun 
              abstract [] t = insert_bounds varmapping t |
              abstract (x::xs) t = (Const (\<^const_name>\<open>Pure.all\<close>,dummyT)) $ (Abs (x, dummyT, abstract xs t))          
          in
            if null vars then t else (abstract varnames t)
          end

(* Adds functions that convert a type to and from its product-sum representation *)
fun define_prod_sum_conv (ty_info : type_info) constr_names lthy = 
  let
    val tnames = #mutual_tnames ty_info 
    val Ts = #mutual_Ts ty_info
    val ctrs = #mutual_ctrs ty_info
    val sels = #mutual_sels ty_info
    val is_recursive = #is_rec ty_info
    val is_mutually_recursive = #is_mutually_rec ty_info

    val _ = map (fn tyco => "Generating conversions for type " ^ quote tyco) tnames
      |> cat_lines |> writeln

    (* Functions to deal with tagged products and sums *)
    val str_optT = \<^typ>\<open>string option\<close>
    val none_str_opt = Const (\<^const_name>\<open>None\<close>, str_optT)
    fun some_str s = Const (\<^const_name>\<open>Some\<close>, \<^typ>\<open>string\<close> --> str_optT) $ HOLogic.mk_string s
    val dummy_str_opt = (Term.dummy_pattern \<^typ>\<open>string option\<close>)
    val sum_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.sum\<close> else \<^type_name>\<open>Sum_Type.sum\<close>
    val prod_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.prod\<close> else \<^type_name>\<open>Product_Type.prod\<close>
    val prod_constr_name = if constr_names then \<^const_name>\<open>Tagged_Prod_Sum.Prod\<close> else \<^const_name>\<open>Product_Type.Pair\<close>
    val inl_constr_name = if constr_names then \<^const_name>\<open>Tagged_Prod_Sum.Inl\<close> else \<^const_name>\<open>Sum_Type.Inl\<close>
    val inr_constr_name = if constr_names then \<^const_name>\<open>Tagged_Prod_Sum.Inr\<close> else \<^const_name>\<open>Sum_Type.Inr\<close>
    fun mk_tagged_prodT (T1, T2) = Type (prod_type_name, [T1, T2])
    fun mk_tagged_sumT LT RT = Type (sum_type_name, [LT, RT])
    fun tagged_pair_const T1 T2 = Const (prod_constr_name, str_optT --> str_optT --> T1 --> T2 --> mk_tagged_prodT (T1, T2));
    fun mk_tagged_prod ((t1,s1), (t2,s2)) =
      let val T1 = fastype_of t1 
          val T2 = fastype_of t2 
          val S1 = if s1 = "" then none_str_opt else some_str s1
          val S2 = if s2 = "" then none_str_opt else some_str s2
      in
        (tagged_pair_const T1 T2 $ S1 $ S2 $ t1 $ t2,"")
      end
    fun mk_tagged_prod_dummy (t1, t2) =
      let val T1 = fastype_of t1 and T2 = fastype_of t2 in
        tagged_pair_const T1 T2 $ dummy_str_opt $ dummy_str_opt $ t1 $ t2
      end
    fun Inl_const LT RT = if constr_names then Const (inl_constr_name, str_optT --> LT --> mk_tagged_sumT LT RT) else BNF_FP_Util.Inl_const LT RT
    fun mk_tagged_Inl n RT t = Inl_const (fastype_of t) RT $ n $ t
    fun Inr_const LT RT = if constr_names then Const (inr_constr_name, str_optT --> RT --> mk_tagged_sumT LT RT) else BNF_FP_Util.Inr_const LT RT
    fun mk_tagged_tuple _ [] = HOLogic.unit
      | mk_tagged_tuple sels ts = fst (foldr1 mk_tagged_prod (ts ~~ sels))
    fun mk_tagged_tuple_dummy [] = HOLogic.unit
      | mk_tagged_tuple_dummy ts = foldr1 mk_tagged_prod_dummy ts
    fun add_dummy_patterns (c $ _) = c $ dummy_str_opt |
            add_dummy_patterns t = t

    (* simple version for non-recursive types *)
    fun generate_conversion_eqs lthy prefix ((tyco,ctrs),T) sels =
      let
        fun 
          mk_prod_listT [] = HOLogic.unitT |
          mk_prod_listT [x] = x |
          mk_prod_listT (x::xs) = mk_tagged_prodT (x, (mk_prod_listT xs))
        fun generate_sum_prodT [] = HOLogic.unitT |
            generate_sum_prodT [x] = mk_prod_listT x |
            generate_sum_prodT (x::xs) = 
              let 
                val l = mk_prod_listT x
                val r = generate_sum_prodT xs
              in
                mk_tagged_sumT l r
              end
        
        fun generate_conversion_eq lthy prefix (cN, Ts) sels tail_ctrs = 
          let           
            val c = Const (cN, Ts ---> T)
            val sels = if null sels then replicate (length Ts) "" else sels
            val cN_opt = Const (\<^const_name>\<open>Some\<close>, \<^typ>\<open>string\<close> --> str_optT) $ HOLogic.mk_string (Long_Name.base_name cN)
            val xs = map Free (Name.invent_names (Variable.names_of lthy) "x" Ts)
            
            val conv_inner = case tail_ctrs of 
                              [] => if constr_names then mk_tagged_tuple sels xs else HOLogic.mk_tuple xs |
                              _ => if constr_names then mk_tagged_Inl cN_opt (generate_sum_prodT tail_ctrs) (mk_tagged_tuple sels xs) 
                                                   else BNF_FP_Util.mk_Inl (generate_sum_prodT tail_ctrs) (HOLogic.mk_tuple xs)
            val prefix = case tail_ctrs of
                          [] => if constr_names andalso (not (HOLogic.is_unit (hd prefix)))
                                  then 
                                    (let val (butlast,last) = split_last prefix 
                                     in butlast @ [last |> dest_comb |> fst |> (fn t => t $ cN_opt)]
                                     end)
                                  else prefix |
                          _ => prefix
            val conv = if HOLogic.is_unit (hd prefix) 
                      then conv_inner
                      else Library.foldr (op $) (prefix,conv_inner)
            val conv_dummy = if constr_names 
                               then (let val conv_inner = 
                                             case tail_ctrs of 
                                                [] => mk_tagged_tuple sels xs|
                                                _ => mk_tagged_Inl (Term.dummy_pattern \<^typ>\<open>string option\<close>) (generate_sum_prodT tail_ctrs) (mk_tagged_tuple_dummy xs)
                                     in (if HOLogic.is_unit (hd prefix) then conv_inner 
                                                                        else Library.foldr (op $) ((map add_dummy_patterns prefix), conv_inner))
                                     end)
                               else conv
            val lhs_from = (Free ("from_" ^ (Long_Name.base_name tyco), dummyT)) $ list_comb (c, xs) 
            val lhs_to = (Free ("to_" ^ (Long_Name.base_name tyco), dummyT)) $ conv_dummy 
          in (abstract_over_vars xs (HOLogic.Trueprop $ ((HOLogic.eq_const dummyT) $ lhs_from $ conv)),
              abstract_over_vars xs (HOLogic.Trueprop $ ((HOLogic.eq_const dummyT) $ lhs_to $ list_comb(c,xs))))
        end
      in
        case ctrs of 
          [] => ([],[]) |
          (c::cs) => 
            let 
              val s = if null sels then replicate (length (snd c)) "" else hd sels
              val ss = if null sels then [] else tl sels
              val new_prefix = 
                  if HOLogic.is_unit (hd prefix) 
                  then 
                    if constr_names 
                      then [(Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs))) $ Const (\<^const_name>\<open>None\<close>, str_optT)]
                      else [(BNF_FP_Util.Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs)))]
                  else prefix @
                    (if constr_names
                      then [(Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs))) $ Const (\<^const_name>\<open>None\<close>, str_optT)]
                      else [(BNF_FP_Util.Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs)))])
              val (from_eq,to_eq) = generate_conversion_eq lthy prefix c s (map snd cs)
              val (from_eqs,to_eqs) = generate_conversion_eqs lthy new_prefix ((tyco,cs),T) ss
            in 
                (from_eq :: from_eqs, to_eq :: to_eqs)
            end
      end  

    (* version for recursive types *)
    fun generate_conversion_eqs_rec lthy Ts comb_type (((tyco,ctrs),T),prefix) sels =
      let
        fun replace_type_with_comb T =
          case List.find (fn x => x = T) Ts of
            NONE => T |
            _    => comb_type
        fun mk_prod_listT [] = HOLogic.unitT |
            mk_prod_listT [x] = replace_type_with_comb x |
            mk_prod_listT (x::xs) = mk_tagged_prodT (replace_type_with_comb x, (mk_prod_listT xs))
        fun generate_sum_prodT [] = HOLogic.unitT |
            generate_sum_prodT [x] = mk_prod_listT x |
            generate_sum_prodT (x::xs) = 
              let 
                val l = mk_prod_listT x
                val r = generate_sum_prodT xs
              in
                mk_tagged_sumT l r
              end
        
        fun generate_conversion_eq lthy prefix (cN, Ts) sels tail_ctrs = 
          let 
            fun get_type_name T = case T of Type (s,_) => s | _ => ""
            fun find_type T tycos = List.find (fn x => x = (get_type_name T) andalso x <> "") tycos 
            fun mk_comb_type v = Free (v |> dest_Free |> fst,comb_type)
            fun from_const tyco = Free ("from_" ^ (Long_Name.base_name tyco), dummyT --> dummyT)
            fun to_const tyco = Free ("to_" ^ (Long_Name.base_name tyco), dummyT --> dummyT)
            val c = Const (cN, Ts ---> T)
            val cN_opt = Const (\<^const_name>\<open>Some\<close>, \<^typ>\<open>string\<close> --> str_optT) $ HOLogic.mk_string (Long_Name.base_name cN)
            val xs = map Free (Name.invent_names (Variable.names_of lthy) "x" Ts)
            
            val xs_from = map (fn (v,t) => case find_type t tnames 
                                           of NONE => v |
                                              _    => (from_const (get_type_name t)) $ v)
                          (xs ~~ Ts)
            val xs_to   = map (fn (v,t) => case find_type t tnames 
                                           of NONE => v |
                                              _    => (to_const (get_type_name t)) $ mk_comb_type v)
                          (xs ~~ Ts)
            val xs_to'  = map (fn (v,t) => case find_type t tnames 
                                           of NONE => v |
                                              _    => mk_comb_type v)
                          (xs ~~ Ts) 

            val prefix = case tail_ctrs of
                          [] => if constr_names andalso (not (HOLogic.is_unit (hd prefix)))
                                  then 
                                    (let val (butlast,last) = split_last prefix 
                                     in butlast @ [last |> dest_comb |> fst |> (fn t => t $ cN_opt)]
                                     end)
                                  else prefix |
                          _ => prefix

            val conv_inner_from = case tail_ctrs of 
                              [] => if constr_names then mk_tagged_tuple sels xs_from else HOLogic.mk_tuple xs_from |
                              _ => if constr_names then mk_tagged_Inl cN_opt (generate_sum_prodT tail_ctrs) (mk_tagged_tuple sels xs_from)
                                                   else BNF_FP_Util.mk_Inl (generate_sum_prodT tail_ctrs) (HOLogic.mk_tuple xs_from)
            val conv_inner_to = case tail_ctrs of 
                              [] => if constr_names then mk_tagged_tuple_dummy xs_to' else HOLogic.mk_tuple xs_to' |
                              _ => if constr_names then mk_tagged_Inl dummy_str_opt (generate_sum_prodT tail_ctrs) (mk_tagged_tuple_dummy xs_to')
                                                   else BNF_FP_Util.mk_Inl (generate_sum_prodT tail_ctrs) (HOLogic.mk_tuple xs_to')
            val conv_from = if HOLogic.is_unit (hd prefix) 
                            then conv_inner_from
                            else Library.foldr (op $) (prefix,conv_inner_from)
            val conv_to = if HOLogic.is_unit (hd prefix) 
                            then conv_inner_to
                            else Library.foldr (op $) (prefix,conv_inner_to)  
            val conv_dummy = if constr_names 
                               then (let val conv_inner = 
                                             case tail_ctrs of 
                                               [] => mk_tagged_tuple_dummy xs_to' |
                                               _ => mk_tagged_Inl dummy_str_opt (generate_sum_prodT tail_ctrs) (mk_tagged_tuple_dummy xs_to')
                                     in (if HOLogic.is_unit (hd prefix) then conv_inner 
                                                                        else Library.foldr (op $) ((map add_dummy_patterns prefix), conv_inner))
                                     end)
                               else conv_to
                      

            val lhs_from = (from_const tyco) $ list_comb (c, xs) 
            val lhs_to = (to_const tyco) $ conv_dummy 
          in (abstract_over_vars xs (HOLogic.Trueprop $ ((HOLogic.eq_const dummyT) $ lhs_from $ conv_from)),
              abstract_over_vars xs (HOLogic.Trueprop $ ((HOLogic.eq_const dummyT) $ lhs_to $ list_comb (c,xs_to))))
        end
      in
        case ctrs of 
          [] => ([],[]) |
          (c::cs) => 
            let  
              val s = if null sels then replicate (length (snd c)) "" else hd sels
              val ss = if null sels then [] else tl sels
              val new_prefix = 
                  if HOLogic.is_unit (hd prefix) 
                  then 
                    if constr_names 
                      then [(Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs))) $ Const (\<^const_name>\<open>None\<close>, str_optT)]
                      else [(BNF_FP_Util.Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs)))]
                  else prefix @
                    (if constr_names
                      then [(Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs))) $ Const (\<^const_name>\<open>None\<close>, str_optT)]
                      else [(BNF_FP_Util.Inr_const (generate_sum_prodT [(snd c)]) (generate_sum_prodT (map snd cs)))])

              val (from_eq,to_eq) = generate_conversion_eq lthy prefix c s (map snd cs)
              val (from_eqs,to_eqs) = generate_conversion_eqs_rec lthy Ts comb_type (((tyco,cs),T),new_prefix) ss
            in
                (from_eq :: from_eqs, to_eq :: to_eqs)
            end
      end  

      fun generate_mutual_prefixes inConst Ts mutual_rep_types =
        let
          fun generate_sumT [] = HOLogic.unitT |
              generate_sumT [x] = x |
              generate_sumT (x::xs) = mk_tagged_sumT x (generate_sumT xs)
          fun generate_mutual_prefix rep_types index = 
          let
            fun generate_mutual_prefix_aux rep_types index =
              case index of
                0 => if constr_names 
                       then [(Inl_const (hd rep_types) (generate_sumT (tl rep_types))) $ none_str_opt]
                       else [Inl_const (hd rep_types) (generate_sumT (tl rep_types))] |
                n => let 
                      val inr = if constr_names
                                  then (Inr_const (hd rep_types) (generate_sumT (tl rep_types))) $ none_str_opt 
                                  else Inr_const (hd rep_types) (generate_sumT (tl rep_types)) 
                     in
                       if (length rep_types) > 2 then inr :: (generate_mutual_prefix_aux (tl rep_types) (n-1))
                                                 else [inr]
                     end
          in
            inConst :: (generate_mutual_prefix_aux rep_types index)
          end

          val indices = List.tabulate (length Ts, fn x => x)
        in
          (map (generate_mutual_prefix mutual_rep_types) indices)
        end
        
      fun add_functions lthy =
        let 
          val eqs = 
            if is_recursive
            then
              let
                fun get_mutual_rep_types ty n =
                   if n = 1 then [ty] else
                     case ty of
                       Type (tname, [LT, RT]) => if tname = sum_type_name then LT :: (get_mutual_rep_types RT (n-1)) else [Type (tname, [LT, RT])] |
                       T => [T]
                val comb_type = #comb_type (the (#comb_info ty_info))
                val inConst_free = #inConst_free (the (#comb_info ty_info))
                val rep_type_inst = #rep_type_instantiated (the (#comb_info ty_info))         
                val mutual_rep_types = if is_mutually_recursive then get_mutual_rep_types rep_type_inst (length Ts)
                                                                else [rep_type_inst]
                val prefixes = if is_mutually_recursive then generate_mutual_prefixes inConst_free Ts mutual_rep_types
                                                        else replicate (length Ts) [inConst_free]
              in 
                map2 (generate_conversion_eqs_rec lthy Ts comb_type)  ((ctrs ~~ Ts) ~~ prefixes) (map snd sels)
              end
            else
              map2 (generate_conversion_eqs lthy [HOLogic.unit]) (ctrs ~~ Ts) (map snd sels)
          val from_eqs = flat (map fst eqs)
          val to_eqs = flat (map snd eqs)
          val (from_info,lthy') = 
            add_fun' 
              (map (fn tname => (Binding.name ("from_" ^ Long_Name.base_name tname), NONE, NoSyn)) tnames) 
              (map (fn t => ((Binding.empty_atts, t), [], []))
                from_eqs)
              Function_Fun.fun_config 
              lthy
          val (to_info,lthy'') =
            add_fun' 
              (map (fn tname => (Binding.name ("to_" ^ Long_Name.base_name tname), NONE, NoSyn)) tnames) 
              (map (fn t => ((Binding.empty_atts, t), [], []))
                to_eqs)
              Function_Fun.fun_config
              lthy'
        in 
          (from_info,to_info,lthy'')
        end
      
    in
      add_functions lthy
  end

fun define_rep_type tnames ctrs constr_names lthy = 
  let
    val sum_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.sum\<close> else \<^type_name>\<open>Sum_Type.sum\<close>
    val prod_type_name = if constr_names then \<^type_name>\<open>Tagged_Prod_Sum.prod\<close> else \<^type_name>\<open>Product_Type.prod\<close>
    fun collect_tfree_names ctrs = 
      fold Term.add_tfree_namesT (ctrs |> map (fn l => map snd (snd l)) |> flat |> flat) []

    val tFree_renaming =
      let
        val used_tfrees = collect_tfree_names ctrs
        val ctxt = Name.make_context used_tfrees
        val ts = map Type ((map fst ctrs) ~~ (replicate (length ctrs) []))
        val names = Name.invent_names ctxt "'a" ts |> map fst
      in
        ts ~~ (map TFree (names ~~ (replicate (length names) \<^sort>\<open>type\<close>))) 
      end

    fun replace_types_tvars recTs T  =
      (case T of Type  (s,_) => perhaps (AList.lookup (op =) recTs) (Type (s, []))
               | _ => T)

    fun mk_tagged_prodT (T1, T2) = Type (prod_type_name, [T1, T2])
    fun mk_tagged_sumT LT RT = Type (sum_type_name, [LT, RT])

    val rep_type =
      let 
        val ctrs' = (ctrs |> map (fn l => map snd (snd l)))
        fun 
          mk_prodT [] = HOLogic.unitT |
          mk_prodT [x] = replace_types_tvars tFree_renaming x |
          mk_prodT (x::xs) = mk_tagged_prodT (replace_types_tvars tFree_renaming x, (mk_prodT xs))
        fun
          mk_sumT [] = HOLogic.unitT |
          mk_sumT [x] = x |
          mk_sumT (x::xs) = mk_tagged_sumT x (mk_sumT xs)
        fun generate_rep_type_aux []  = HOLogic.unitT |
            generate_rep_type_aux [x] = mk_prodT x |
            generate_rep_type_aux (x::xs) = 
              let 
                val l = mk_prodT x
                val r = generate_rep_type_aux xs
              in
                mk_tagged_sumT l r
              end
        in mk_sumT (map generate_rep_type_aux ctrs')
      end

    val rep_type_name = fold (curry (op ^)) (map Long_Name.base_name tnames) "" ^ "_rep"
    val tfrees = (collect_tfree_names ctrs) @ 
                 (map (snd #> (dest_TFree #> fst)) tFree_renaming)
    val _ = writeln ("Defining representation type " ^ rep_type_name)
    val (full_rep_name,lthy') = Typedecl.abbrev (Binding.name rep_type_name, tfrees, NoSyn) rep_type lthy
  in 
    ({repname = full_rep_name,
      rep_type = rep_type,
      tFrees_mapping = tFree_renaming,
      from_info = NONE,
      to_info = NONE} : rep_type_info 
    , lthy')
  end

fun get_combinator_info comb_type_name ctr_type lthy = 
  let
    val inConst = Proof_Context.read_const {proper = true, strict = true} lthy "In"
    val inConstType = inConst |> dest_Const |> snd |> Derive_Util.freeify_tvars
    val inConst_free = Const (inConst |> dest_Const |> fst, inConstType)
    val comb_type = inConstType |> body_type
    val comb_type_name_full = comb_type |> dest_Type |> fst
    val rep_type_instantiated = inConstType |> binder_types |> hd
  in
    {combname = comb_type_name,
     combname_full = comb_type_name_full,
     comb_type = comb_type,
     ctr_type = ctr_type,
     inConst = inConst,
     inConst_free = inConst_free,
     inConst_type = inConstType,
     rep_type_instantiated = rep_type_instantiated} : comb_type_info
  end

fun define_combinator_type tnames tfrees (rep_info : rep_type_info) lthy =
  let
    val comb_type_name = "mu" ^ (fold (curry (op ^)) (map Long_Name.base_name tnames) "") ^ "F"      
    val rec_tfrees = map (dest_TFree o snd) (#tFrees_mapping rep_info)
    val rec_tfree_names = map fst rec_tfrees        
    val rep_tfree_names = (map (fst o dest_TFree o fst) tfrees)
    val comb_type_name_tvars = add_tvars comb_type_name rep_tfree_names
    val rec_type = (Type (comb_type_name,map fst tfrees))
    val ctr_tfree_names = rep_tfree_names @ (replicate (length rec_tfree_names) comb_type_name_tvars)    
    val ctr_type_name = add_tvars (#repname rep_info) ctr_tfree_names 
    val ctr_type = map_type_tfree (fn (tfree,s) => case List.find (curry (op =) tfree) rec_tfree_names of
                                                    SOME _ => rec_type |
                                                    NONE   => TFree (tfree,s))
                                  (#rep_type rep_info)
    val ctr_typarams = ((replicate (length tfrees) (SOME Binding.empty)) ~~ (rep_tfree_names ~~ (replicate (length tfrees) NONE)))
    val ctr_specs = [(((Binding.empty, Binding.name "In"), [(Binding.empty, ctr_type_name)]), NoSyn)]
    val _ = writeln ("Defining combinator type " ^ comb_type_name)    
    val lthy' = 
      BNF_FP_Def_Sugar.co_datatype_cmd BNF_Util.Least_FP BNF_LFP.construct_lfp 
        ((K Plugin_Name.default_filter, false), 
            [(((((ctr_typarams, Binding.name comb_type_name), NoSyn),
             ctr_specs)
             ,(Binding.empty, Binding.empty, Binding.empty))
            ,[])]) lthy
    val comb_info = get_combinator_info comb_type_name ctr_type lthy'
  in
    (SOME comb_info
    , lthy')
  end

fun generate_type_info tname constr_names lthy = 
  let
    val (tnames, Ts) = Derive_Util.mutual_recursive_types tname lthy
    (* get constructor and selector information from the BNF package *)
    fun get_ctrs t = (t,map (apsnd (map Derive_Util.freeify_tvars o fst o strip_type) o dest_Const)
                            (Derive_Util.constr_terms lthy t))
    fun get_sels t = (t,Ctr_Sugar.ctr_sugar_of lthy t |> the |> #selss 
                          |> (map (map (dest_Const #> fst #> Long_Name.base_name))))
    val ctrs = map get_ctrs tnames
    val sels = map get_sels tnames
    val tfrees = collect_tfrees ctrs
    val is_mutually_rec = (length tnames) > 1
    (* look for recursive constructor arguments *)
    val is_rec = ctrs_arguments ctrs |> filter is_typeT |> map (dest_Type #> fst)
                    |> List.exists (fn n => is_some (List.find (curry (op =) n) tnames))
    val (rep_info,lthy') = define_rep_type tnames ctrs constr_names lthy
    val (comb_info,lthy'') = if is_rec then define_combinator_type tnames tfrees rep_info lthy'
                                       else (NONE,lthy')
  in
    ({tname = tname,
     uses_metadata = constr_names,
     tfrees = tfrees,
     mutual_tnames = tnames,
     mutual_Ts = Ts,
     mutual_ctrs = ctrs,
     mutual_sels = sels,
     is_rec = is_rec,
     is_mutually_rec = is_mutually_rec,
     rep_info = rep_info,
     comb_info = comb_info,
     iso_thm = NONE} : type_info
    , lthy'')
  end

fun generate_class_info class = 
  {classname = hd class,
   class = class,
   params = NONE,
   class_law = NONE,
   class_law_const = NONE,
   ops = NONE,
   transfer_law = NONE,
   axioms = NONE,
   axioms_def = NONE,
   class_def = NONE,
   equivalence_thm = NONE}

fun record_type_class_info ty_info cl_info inst_info thy =  
  let 
    fun add_info info thy = Type_Data.put (Symtab.update (mk_key (#tname info) (#uses_metadata info),info) (Type_Data.get thy)) thy
    fun add_inst_info classname tname thy = Instance_Data.put (Symtab.update (hash_string (classname^tname),inst_info) (Instance_Data.get thy)) thy
    fun update_tname ({tname = _, uses_metadata = uses_metadata, tfrees = tfrees, mutual_tnames = mutual_tnames,
                     mutual_Ts = mutual_Ts, mutual_ctrs = mutual_ctrs, mutual_sels = mutual_sels, is_rec = is_rec,
                     is_mutually_rec = is_mutually_rec, rep_info = rep_info, comb_info = comb_info, iso_thm = iso_thm} : type_info)
                     tname = 
      {tname = tname, uses_metadata = uses_metadata, tfrees = tfrees, mutual_tnames = mutual_tnames,
                     mutual_Ts = mutual_Ts, mutual_ctrs = mutual_ctrs, mutual_sels = mutual_sels, is_rec = is_rec,
                     is_mutually_rec = is_mutually_rec, rep_info = rep_info, comb_info = comb_info, iso_thm = iso_thm} : type_info
    val infos = map (update_tname ty_info) (#mutual_tnames ty_info)                    
  in
    fold add_info infos thy 
  |> Class_Data.put (Symtab.update ((#classname cl_info),cl_info) (Class_Data.get thy))
  |> fold (add_inst_info (#classname cl_info)) (#mutual_tnames ty_info) 
  end

fun generate_instance tname class constr_names thy =
  let
    val (T,xs) = Derive_Util.typ_and_vs_of_typname thy tname class 
    val has_law = has_class_law (hd class) thy
    val cl_info = 
      case get_class_info thy (hd class) of
        NONE => if has_law then error ("Class " ^ (hd class) ^ "not set up for derivation, call derive_setup first")
                                            else generate_class_info class |
        SOME info => info
    val raw_params = map snd (Class.these_params thy class)
    val cl_info' = add_params_cl_info cl_info raw_params
    val thy' = Class_Data.put (Symtab.update ((#classname cl_info'),cl_info') (Class_Data.get thy)) thy
    val lthy = Named_Target.theory_init thy'
    val (ty_info,lthy') = 
      case get_type_info thy tname constr_names of
        SOME info => let
                       val _ = writeln ("Using existing type information for " ^ tname)
                     in (info,lthy) 
                     end |
        NONE => let
                  val (t_info,lthy) = generate_type_info tname constr_names lthy 
                  val (from_info,to_info,lthy') = define_prod_sum_conv t_info constr_names lthy
                  val t_info' = add_conversion_info from_info to_info t_info
                  val (iso_thm,lthy'') = if has_law then Derive_Laws.prove_isomorphism t_info' lthy'
                                                    else (NONE,lthy')
                  val t_info'' = add_iso_info iso_thm t_info'                        
                in
                  (t_info'',lthy'')
                end
                                    
    val tnames = #mutual_tnames ty_info
    val Ts = (map (fn tn => Derive_Util.typ_and_vs_of_typname thy tn class) tnames) |> map fst
    fun define_operations_all_Ts _ lthy =
      let 
        val (thms,lthy') = fold_map (define_operations raw_params) (tnames ~~ Ts) lthy |> apfst flat
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy')
        val thms_export = Proof_Context.export lthy' ctxt_thy thms
        val inst_info = mk_inst_info thms_export
      in (inst_info,lthy') 
      end

    fun instantiate_and_prove _ lthy =
      Local_Theory.exit_global lthy
      |> (Class.instantiation (tnames, xs, class))
      |> define_operations_all_Ts cl_info'
      |> (fn (inst_info,lthy) => 
          (if has_law 
            then
              let 
                val equivalence_thm = (Derive_Laws.prove_equivalence_law cl_info inst_info lthy)
                val cl_info'' = add_equivalence_cl_info cl_info' equivalence_thm
              in                                              
                (Class.prove_instantiation_exit (Derive_Laws.prove_instance_tac T cl_info'' inst_info ty_info) lthy) |> pair cl_info'' |> pair inst_info
              end
            else (Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt []) lthy) |> pair cl_info |> pair inst_info))
      |> (fn (inst_info,(cl_info,thy)) => record_type_class_info ty_info cl_info inst_info thy)
      |> Proof_Context.init_global

    val empty_goal = [[]]
      
    (* Generate instance for Mu-combinator type if there is recursion *)
    val thy' = if (#is_rec ty_info) then (instantiate_combinator_type ty_info cl_info' constr_names lthy' 
                                      |> (if is_some (#class_law cl_info') 
                                            then Derive_Laws.prove_combinator_instance instantiate_and_prove
                                            else
                                                Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [])
                                                #> Named_Target.theory_init
                                                #> Proof.theorem NONE instantiate_and_prove empty_goal))
                                    else Proof.theorem NONE instantiate_and_prove empty_goal lthy'
  in
    thy' 
  end

fun generate_instance_cmd classname tyco constr_names thy =
  let
    val lthy = Proof_Context.init_global thy
    val T = Syntax.parse_typ lthy tyco |> dest_Type |> fst
    val class = Syntax.parse_sort (Proof_Context.init_global thy) classname
  in
    generate_instance T class constr_names thy
  end

val parse_cmd =
      Scan.optional (Args.parens (Parse.reserved "metadata")) ""  --
      Parse.name --
      Parse.type_const

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>derive_generic\<close> "derives some sort"
    (parse_cmd >> (fn ((s,c),t) =>
      let val meta = s = "metadata" in Toplevel.theory_to_proof (generate_instance_cmd c t meta) end ))

fun add_inst_info classname tname thms thy = 
  Instance_Data.put (Symtab.update (hash_string (classname^tname),{defs = thms}) (Instance_Data.get thy)) thy

end
