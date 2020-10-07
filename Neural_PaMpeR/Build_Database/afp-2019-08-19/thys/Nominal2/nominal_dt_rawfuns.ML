(*  Title:      nominal_dt_rawfuns.ML
    Author:     Cezary Kaliszyk
    Author:     Christian Urban

  Definitions of the raw fv, fv_bn and permute functions.
*)

signature NOMINAL_DT_RAWFUNS =
sig
  val get_all_binders: bclause list -> (term option * int) list
  val is_recursive_binder: bclause -> bool

  val define_raw_bns: raw_dt_info -> (binding * typ option * mixfix) list ->
    Specification.multi_specs -> local_theory ->
    (term list * thm list * bn_info list * thm list * local_theory)

  val define_raw_fvs: raw_dt_info -> bn_info list -> bclause list list list ->
    Proof.context -> term list * term list * thm list * thm list * local_theory

  val define_raw_bn_perms: raw_dt_info -> bn_info list -> local_theory ->
    (term list * thm list * local_theory)

  val define_raw_perms: raw_dt_info -> local_theory -> (term list * thm list * thm list) * local_theory

  val raw_prove_eqvt: term list -> thm list -> thm list -> Proof.context -> thm list

end


structure Nominal_Dt_RawFuns: NOMINAL_DT_RAWFUNS =
struct

open Nominal_Permeq

fun get_all_binders bclauses =
  bclauses
  |> map (fn (BC (_, binders, _)) => binders)
  |> flat
  |> remove_dups (op =)

fun is_recursive_binder (BC (_, binders, bodies)) =
  case (inter (op =) (map snd binders) bodies) of
    nil => false
  | _ => true


fun lookup xs x = the (AList.lookup (op=) xs x)


(** functions that define the raw binding functions **)

(* strip_bn_fun takes a rhs of a bn function: this can only contain unions or
   appends of elements; in case of recursive calls it returns also the applied
   bn function *)
fun strip_bn_fun ctxt args t =
let
  fun aux t =
    case t of
      Const (@{const_name sup}, _) $ l $ r => aux l @ aux r
    | Const (@{const_name append}, _) $ l $ r => aux l @ aux r
    | Const (@{const_name insert}, _) $ (Const (@{const_name atom}, _) $ (x as Var _)) $ y =>
        (find_index (equal x) args, NONE) :: aux y
    | Const (@{const_name Cons}, _) $ (Const (@{const_name atom}, _) $ (x as Var _)) $ y =>
        (find_index (equal x) args, NONE) :: aux y
    | Const (@{const_name bot}, _) => []
    | Const (@{const_name Nil}, _) => []
    | (f as Const _) $ (x as Var _) => [(find_index (equal x) args, SOME f)]
    | _ => error ("Unsupported binding function: " ^ (Syntax.string_of_term ctxt t))
in
  aux t
end

(** definition of the raw binding functions **)

fun prep_bn_info ctxt dt_names dts bn_funs eqs =
let
  fun process_eq eq =
  let
    val (lhs, rhs) = eq
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
    val (bn_fun, [cnstr]) = strip_comb lhs
    val (_, ty) = dest_Const bn_fun
    val (ty_name, _) = dest_Type (domain_type ty)
    val dt_index = find_index (fn x => x = ty_name) dt_names
    val (cnstr_head, cnstr_args) = strip_comb cnstr
    val cnstr_name = Long_Name.base_name (fst (dest_Const cnstr_head))
    val rhs_elements = strip_bn_fun ctxt cnstr_args rhs
  in
    ((bn_fun, dt_index), (cnstr_name, rhs_elements))
  end

  (* order according to constructor names *)
  fun cntrs_order ((bn, dt_index), data) =
  let
    val dt = nth dts dt_index
    val cts = snd dt
    val ct_names = map (Binding.name_of o (fn (x, _, _) => x)) cts
  in
    (bn, (bn, dt_index, order (op=) ct_names data))
  end
in
  eqs
  |> map process_eq
  |> AList.group (op=)      (* eqs grouped according to bn_functions *)
  |> map cntrs_order        (* inner data ordered according to constructors *)
  |> order (op=) bn_funs    (* ordered according to bn_functions *)
end

fun define_raw_bns raw_dt_info raw_bn_funs raw_bn_eqs lthy =
  if null raw_bn_funs
  then ([], [], [], [], lthy)
  else
    let
      val RawDtInfo
        {raw_dt_names, raw_dts, raw_inject_thms, raw_distinct_thms, raw_size_thms, ...} = raw_dt_info

      val lthy1 = Local_Theory.subtarget (Function.add_function raw_bn_funs raw_bn_eqs
        Function_Common.default_config (pat_completeness_simp (raw_inject_thms @ raw_distinct_thms))
        #> snd) lthy;

      val ({fs, simps, inducts, ...}, lthy2) =
        prove_termination_fun raw_size_thms    lthy1

      val raw_bn_induct = the inducts
      val raw_bn_eqs = the simps

      val raw_bn_info =
        prep_bn_info lthy raw_dt_names raw_dts fs (map Thm.prop_of raw_bn_eqs)
    in
      (fs, raw_bn_eqs, raw_bn_info, raw_bn_induct, lthy2)
    end



(** functions that construct the equations for fv and fv_bn **)

fun mk_fv_rhs lthy fv_map fv_bn_map args (BC (bmode, binders, bodies)) =
  let
    fun mk_fv_body i =
      let
        val arg = nth args i
        val ty = fastype_of arg
      in
        case AList.lookup (op=) fv_map ty of
          NONE => mk_supp arg
        | SOME fv => fv $ arg
      end

    fun bind_set (NONE, i) = (setify lthy (nth args i), @{term "{}::atom set"})
      | bind_set (SOME bn, i) = (bn $ (nth args i),
          if  member (op=) bodies i then @{term "{}::atom set"}
          else lookup fv_bn_map bn $ (nth args i))

    fun bind_lst (NONE, i) = (listify lthy (nth args i), @{term "[]::atom list"})
      | bind_lst (SOME bn, i) = (bn $ (nth args i),
          if  member (op=) bodies i then @{term "[]::atom list"}
          else lookup fv_bn_map bn $ (nth args i))

    val (combine_fn, bind_fn) =
      case bmode of
        Lst => (fold_append, bind_lst)
      | Set => (fold_union, bind_set)
      | Res => (fold_union, bind_set)

    val t1 = map mk_fv_body bodies
    val (t2, t3) =
      binders
      |> map bind_fn
      |> split_list
      |> apply2 combine_fn
  in
    mk_union (mk_diff (fold_union t1, to_set t2), to_set t3)
  end

(* in case of fv_bn we have to treat the case special, where an
   "empty" binding clause is given *)
fun mk_fv_bn_rhs lthy fv_map fv_bn_map bn_args args bclause =
  let
    fun mk_fv_bn_body i =
    let
      val arg = nth args i
      val ty = fastype_of arg
    in
      case AList.lookup (op=) bn_args i of
        NONE => (case (AList.lookup (op=) fv_map ty) of
                   NONE => mk_supp arg
                 | SOME fv => fv $ arg)
      | SOME (NONE) => @{term "{}::atom set"}
      | SOME (SOME bn) => lookup fv_bn_map bn $ arg
    end
  in
    case bclause of
      BC (_, [], bodies) => fold_union (map mk_fv_bn_body bodies)
    | _ => mk_fv_rhs lthy fv_map fv_bn_map args bclause
  end

fun mk_fv_eq lthy fv_map fv_bn_map (constr, ty, arg_tys, _) bclauses =
  let
    val arg_names = Old_Datatype_Prop.make_tnames arg_tys
    val args = map Free (arg_names ~~ arg_tys)
    val fv = lookup fv_map ty
    val lhs = fv $ list_comb (constr, args)
    val rhs_trms = map (mk_fv_rhs lthy fv_map fv_bn_map args) bclauses
    val rhs = fold_union rhs_trms
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
  end

fun mk_fv_bn_eq lthy bn_trm fv_map fv_bn_map (bn_args, (constr, _, arg_tys, _)) bclauses =
  let
    val arg_names = Old_Datatype_Prop.make_tnames arg_tys
    val args = map Free (arg_names ~~ arg_tys)
    val fv_bn = lookup fv_bn_map bn_trm
    val lhs = fv_bn $ list_comb (constr, args)
    val rhs_trms = map (mk_fv_bn_rhs lthy fv_map fv_bn_map bn_args args) bclauses
    val rhs = fold_union rhs_trms
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
  end

fun mk_fv_bn_eqs lthy fv_map fv_bn_map constrs_info bclausesss (bn_trm, bn_n, bn_argss) =
  let
    val nth_constrs_info = nth constrs_info bn_n
    val nth_bclausess = nth bclausesss bn_n
  in
    map2 (mk_fv_bn_eq lthy bn_trm fv_map fv_bn_map) (bn_argss ~~ nth_constrs_info) nth_bclausess
  end

fun define_raw_fvs raw_dt_info bn_info bclausesss lthy =
  let
    val RawDtInfo
      {raw_dt_names, raw_tys, raw_cns_info, raw_inject_thms, raw_distinct_thms, raw_size_thms, ...} =
        raw_dt_info

    val fv_names = map (prefix "fv_" o Long_Name.base_name) raw_dt_names
    val fv_tys = map (fn ty => ty --> @{typ "atom set"}) raw_tys
    val fv_frees = map Free (fv_names ~~ fv_tys);
    val fv_map = raw_tys ~~ fv_frees

    val (bns, bn_tys) = split_list (map (fn (bn, i, _) => (bn, i)) bn_info)
    val bn_names = map (fn bn => Long_Name.base_name (fst (dest_Const bn))) bns
    val fv_bn_names = map (prefix "fv_") bn_names
    val fv_bn_arg_tys = map (nth raw_tys) bn_tys
    val fv_bn_tys = map (fn ty => ty --> @{typ "atom set"}) fv_bn_arg_tys
    val fv_bn_frees = map Free (fv_bn_names ~~ fv_bn_tys)
    val fv_bn_map = bns ~~ fv_bn_frees

    val fv_eqs = map2 (map2 (mk_fv_eq lthy fv_map fv_bn_map)) raw_cns_info bclausesss
    val fv_bn_eqs = map (mk_fv_bn_eqs lthy fv_map fv_bn_map raw_cns_info bclausesss) bn_info

    val all_fun_names = map (fn s => (Binding.name s, NONE, NoSyn)) (fv_names @ fv_bn_names)
    val all_fun_eqs = map (fn t => ((Binding.empty_atts, t), [], [])) (flat fv_eqs @ flat fv_bn_eqs)

    val lthy' = Local_Theory.subtarget (Function.add_function all_fun_names all_fun_eqs
      Function_Common.default_config (pat_completeness_simp (raw_inject_thms @ raw_distinct_thms))
      #> snd) lthy

    val ({fs, simps, inducts, ...}, lthy'') = prove_termination_fun raw_size_thms lthy'

    val morphism =
      Proof_Context.export_morphism lthy''
        (Proof_Context.transfer (Proof_Context.theory_of lthy'') lthy)
    val simps_exp = map (Morphism.thm morphism) (the simps)
    val inducts_exp = map (Morphism.thm morphism) (the inducts)

    val (fvs', fv_bns') = chop (length fv_frees) fs

    (* grafting the types so that they coincide with the input into the function package *)
    val fvs'' = map2 (fn t => fn ty => Const (fst (dest_Const t), ty) ) fvs' fv_tys
    val fv_bns'' = map2 (fn t => fn ty => Const (fst (dest_Const t), ty) ) fv_bns' fv_bn_tys
  in
    (fvs'', fv_bns'', simps_exp, inducts_exp, lthy'')
  end


(** definition of raw permute_bn functions **)

fun mk_perm_bn_eq_rhs p perm_bn_map bn_args (i, arg) =
  case AList.lookup (op=) bn_args i of
    NONE => arg
  | SOME (NONE) => mk_perm p arg
  | SOME (SOME bn) => (lookup perm_bn_map bn) $ p $ arg


fun mk_perm_bn_eq lthy bn_trm perm_bn_map bn_args (constr, _, arg_tys, _) =
  let
    val p = Free ("p", @{typ perm})
    val arg_names = Old_Datatype_Prop.make_tnames arg_tys
    val args = map Free (arg_names ~~ arg_tys)
    val perm_bn = lookup perm_bn_map bn_trm
    val lhs = perm_bn $ p $ list_comb (constr, args)
    val rhs = list_comb (constr, map_index (mk_perm_bn_eq_rhs p perm_bn_map bn_args) args)
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
  end

fun mk_perm_bn_eqs lthy perm_bn_map cns_info (bn_trm, bn_n, bn_argss) =
  let
    val nth_cns_info = nth cns_info bn_n
  in
    map2 (mk_perm_bn_eq lthy bn_trm perm_bn_map) bn_argss nth_cns_info
  end

fun define_raw_bn_perms raw_dt_info bn_info lthy =
  if null bn_info
  then ([], [], lthy)
  else
    let
      val RawDtInfo
        {raw_tys, raw_cns_info, raw_inject_thms, raw_distinct_thms, raw_size_thms, ...} = raw_dt_info

      val (bns, bn_tys) = split_list (map (fn (bn, i, _) => (bn, i)) bn_info)
      val bn_names = map (fn bn => Long_Name.base_name (fst (dest_Const bn))) bns
      val perm_bn_names = map (prefix "permute_") bn_names
      val perm_bn_arg_tys = map (nth raw_tys) bn_tys
      val perm_bn_tys = map (fn ty => @{typ "perm"} --> ty --> ty) perm_bn_arg_tys
      val perm_bn_frees = map Free (perm_bn_names ~~ perm_bn_tys)
      val perm_bn_map = bns ~~ perm_bn_frees

      val perm_bn_eqs = map (mk_perm_bn_eqs lthy perm_bn_map raw_cns_info) bn_info

      val all_fun_names = map (fn s => (Binding.name s, NONE, NoSyn)) perm_bn_names
      val all_fun_eqs = map (fn t => ((Binding.empty_atts, t), [], [])) (flat perm_bn_eqs)

      val prod_simps = @{thms prod.inject HOL.simp_thms}

      val lthy' = Local_Theory.subtarget (Function.add_function all_fun_names all_fun_eqs
        Function_Common.default_config (pat_completeness_simp (prod_simps @ raw_inject_thms @ raw_distinct_thms))
        #> snd) lthy

      val ({fs, simps, ...}, lthy'') = prove_termination_fun raw_size_thms lthy'

      val morphism =
        Proof_Context.export_morphism lthy''
          (Proof_Context.transfer (Proof_Context.theory_of lthy'') lthy)
      val simps_exp = map (Morphism.thm morphism) (the simps)
    in
      (fs, simps_exp, lthy'')
    end

(*** raw permutation functions ***)

(** proves the two pt-type class properties **)

fun prove_permute_zero induct bnfs perm_defs perm_fns ctxt =
  let
    val perm_types = map (body_type o fastype_of) perm_fns
    val perm_indnames = Old_Datatype_Prop.make_tnames perm_types

    fun single_goal ((perm_fn, T), x) =
      HOLogic.mk_eq (perm_fn $ @{term "0::perm"} $ Free (x, T), Free (x, T))

    val goals =
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (map single_goal (perm_fns ~~ perm_types ~~ perm_indnames)))

    val map_ids = map BNF_Def.map_ident_of_bnf bnfs
    val rules = @{thm permute_zero} :: perm_defs @ map_ids
    val congs = map BNF_Def.map_cong0_of_bnf bnfs
  in
    Goal.prove ctxt perm_indnames [] goals
      (fn {context = ctxt', ...} =>
        (Old_Datatype_Aux.ind_tac ctxt' induct perm_indnames THEN_ALL_NEW
          asm_simp_tac
            (fold Simplifier.add_cong congs
              (put_simpset HOL_basic_ss ctxt' addsimps rules))) 1)
    |> Old_Datatype_Aux.split_conj_thm
  end


fun prove_permute_plus induct bnfs perm_defs perm_fns ctxt =
  let
    val p = Free ("p", @{typ perm})
    val q = Free ("q", @{typ perm})
    val perm_types = map (body_type o fastype_of) perm_fns
    val perm_indnames = Old_Datatype_Prop.make_tnames perm_types

    fun single_goal ((perm_fn, T), x) = HOLogic.mk_eq
      (perm_fn $ (mk_plus p q) $ Free (x, T), perm_fn $ p $ (perm_fn $ q $ Free (x, T)))

    val goals =
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (map single_goal (perm_fns ~~ perm_types ~~ perm_indnames)))

    val map_comps = map BNF_Def.map_comp_of_bnf bnfs
    val rules = @{thms permute_plus o_def} @ perm_defs @ map_comps
    val congs = map BNF_Def.map_cong0_of_bnf bnfs
  in
    Goal.prove ctxt ("p" :: "q" :: perm_indnames) [] goals
      (fn {context = ctxt', ...} =>
        (Old_Datatype_Aux.ind_tac ctxt' induct perm_indnames THEN_ALL_NEW
          asm_simp_tac
            (fold Simplifier.add_cong congs
              (put_simpset HOL_basic_ss ctxt' addsimps rules))) 1)
    |> Old_Datatype_Aux.split_conj_thm
  end


(* Return the map operator for the given type, along with its list of
argument types, if a map operator exists; otherwise return NONE *)
fun mk_map_of_type lthy (Type (c, tys)) =
  let
    fun mk_map bnf =
      let
        val live = BNF_Def.live_of_bnf bnf
        val t = BNF_Def.mk_map live tys tys (BNF_Def.map_of_bnf bnf)
        val (map_arg_tys, _) = BNF_Util.strip_typeN live (fastype_of t)
      in
        (t, map domain_type map_arg_tys)
      end
  in
    Option.map mk_map (BNF_Def.bnf_of lthy c)
  end
  | mk_map_of_type _ _ = NONE


fun mk_perm_eq lthy ty_perm_assoc cnstr =
  let
    (* permute function with boolean flag indicating recursion *)
    fun mk_perm p ty =
      case (AList.lookup (op=) ty_perm_assoc ty) of
        SOME perm => (perm $ p, true)
      | NONE =>
        (case mk_map_of_type lthy ty of
          SOME (t, tys) =>
          let
            val (ts, recs) = split_list (map (mk_perm p) tys)
          in
            if exists I recs
            then (list_comb (t, ts), true)
            else (perm_const ty $ p, false)
          end
        | NONE => (perm_const ty $ p, false))

    fun lookup_perm p (ty, arg) = fst (mk_perm p ty) $ arg

    val p = Free ("p", @{typ perm})
    val (arg_tys, ty) = strip_type (fastype_of cnstr)

    val arg_names = Name.variant_list ["p"] (Old_Datatype_Prop.make_tnames arg_tys)
    val args = map Free (arg_names ~~ arg_tys)

    val lhs = lookup_perm p (ty, list_comb (cnstr, args))
    val rhs = list_comb (cnstr, map (lookup_perm p) (arg_tys ~~ args))

    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
  in
    ((Binding.empty_atts, eq), [], [])
  end


fun define_raw_perms raw_dt_info lthy =
  let
    val RawDtInfo
      {raw_dt_names, raw_fp_sugars, raw_tys, raw_ty_args, raw_all_cns, raw_induct_thm, ...} = raw_dt_info

    val bnfs = (#fp_nesting_bnfs o hd) raw_fp_sugars
    val perm_fn_names = raw_dt_names
      |> map Long_Name.base_name
      |> map (prefix "permute_")

    val perm_fn_types = map perm_ty raw_tys
    val perm_fn_frees = map Free (perm_fn_names ~~ perm_fn_types)
    val perm_fn_binds = map (fn s => (Binding.name s, NONE, NoSyn)) perm_fn_names

    val perm_eqs = map (mk_perm_eq lthy (raw_tys ~~ perm_fn_frees)) (flat raw_all_cns)

    fun tac ctxt (_, _, simps) =
      Class.intro_classes_tac ctxt [] THEN ALLGOALS (resolve_tac ctxt simps)

    fun morphism phi (fvs, dfs, simps) =
      (map (Morphism.term phi) fvs,
       map (Morphism.thm phi) dfs,
       map (Morphism.thm phi) simps);

    val ((perm_funs, perm_eq_thms), lthy') =
      lthy
      |> Local_Theory.exit_global
      |> Class.instantiation (raw_dt_names, raw_ty_args, @{sort pt})
      |> BNF_LFP_Compat.primrec perm_fn_binds perm_eqs

    val perm_zero_thms = prove_permute_zero raw_induct_thm bnfs perm_eq_thms perm_funs lthy'
    val perm_plus_thms = prove_permute_plus raw_induct_thm bnfs perm_eq_thms perm_funs lthy'
  in
    lthy'
    |> Class.prove_instantiation_exit_result morphism tac
         (perm_funs, perm_eq_thms, perm_zero_thms @ perm_plus_thms)
    ||> Named_Target.theory_init
  end


(** equivarance proofs **)

val eqvt_apply_sym = @{thm eqvt_apply[symmetric]}

fun subproof_tac const_names simps =
  SUBPROOF (fn {prems, context = ctxt, ...} =>
    HEADGOAL
      (simp_tac (put_simpset HOL_basic_ss ctxt addsimps simps)
       THEN' eqvt_tac ctxt (eqvt_relaxed_config addexcls const_names)
       THEN' simp_tac (put_simpset HOL_basic_ss ctxt addsimps (prems @ [eqvt_apply_sym]))))

fun prove_eqvt_tac insts ind_thms const_names simps ctxt =
  HEADGOAL
    (Object_Logic.full_atomize_tac ctxt
     THEN' (DETERM o (Induct_Tacs.induct_tac ctxt insts (SOME ind_thms)))
     THEN_ALL_NEW  subproof_tac const_names simps ctxt)

fun mk_eqvt_goal pi const arg =
  let
    val lhs = mk_perm pi (const $ arg)
    val rhs = const $ (mk_perm pi arg)
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
  end


fun raw_prove_eqvt consts ind_thms simps ctxt =
  if null consts then []
  else
    let
      val ([p], ctxt') = Variable.variant_fixes ["p"] ctxt
      val p = Free (p, @{typ perm})
      val arg_tys =
        consts
        |> map fastype_of
        |> map domain_type
      val (arg_names, ctxt'') =
        Variable.variant_fixes (Old_Datatype_Prop.make_tnames arg_tys) ctxt'
      val args = map Free (arg_names ~~ arg_tys)
      val goals = map2 (mk_eqvt_goal p) consts args
      val insts = map (single o SOME) arg_names
      val const_names = map (fst o dest_Const) consts
    in
      Goal.prove_common ctxt'' NONE [] [] goals (fn {context, ...} =>
        prove_eqvt_tac insts ind_thms const_names simps context)
      |> Proof_Context.export ctxt'' ctxt
    end


end (* structure *)
