(*  Title:      nominal_dt_alpha.ML
    Author:     Christian Urban
    Author:     Cezary Kaliszyk

  Performing quotient constructions, lifting theorems and
  deriving support properties for the quotient types.
*)

signature NOMINAL_DT_QUOT =
sig
  val define_qtypes: (string list * binding * mixfix) list -> typ list -> term list ->
    thm list -> local_theory -> Quotient_Info.quotients list * local_theory

  val define_qconsts: typ list -> (string  * term * mixfix * thm) list -> local_theory ->
    Quotient_Info.quotconsts list * local_theory

  val define_qperms: typ list -> string list -> (string * sort) list ->
    (string * term * mixfix * thm) list -> thm list -> local_theory -> local_theory

  val define_qsizes: typ list -> string list -> (string * sort) list ->
    (string * term * mixfix * thm) list -> local_theory -> local_theory

  val lift_thms: typ list -> thm list -> thm list -> Proof.context -> thm list * Proof.context

  val prove_supports: Proof.context -> thm list -> term list -> thm list
  val prove_fsupp: Proof.context -> typ list -> thm -> thm list -> thm list

  val fs_instance: typ list -> string list -> (string * sort) list -> thm list ->
    local_theory -> local_theory

  val prove_fv_supp: typ list -> term list -> term list -> term list -> term list -> thm list ->
    thm list -> thm list -> thm list -> thm -> bclause list list -> Proof.context -> thm list

  val prove_bns_finite: typ list -> term list -> thm -> thm list -> Proof.context -> thm list

  val prove_perm_bn_alpha_thms: typ list -> term list -> term list -> thm -> thm list -> thm list ->
    thm list -> Proof.context -> thm list

  val prove_permute_bn_thms: typ list -> term list -> term list -> thm -> thm list -> thm list ->
    thm list -> Proof.context -> thm list

  val prove_strong_exhausts: Proof.context -> thm list -> bclause list list list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list

  val prove_strong_induct: Proof.context -> thm -> thm list -> thm list -> bclause list list list ->
    thm list
end

structure Nominal_Dt_Quot: NOMINAL_DT_QUOT =
struct

open Nominal_Permeq

fun lookup xs x = the (AList.lookup (op=) xs x)


(* defines the quotient types *)
fun define_qtypes qtys_descr alpha_tys alpha_trms alpha_equivp_thms lthy =
  let
    val qty_args1 = map2 (fn ty => fn trm => (ty, trm, false)) alpha_tys alpha_trms
    val qty_args2 = map2 (fn descr => fn args1 => (descr, args1, (NONE, NONE))) qtys_descr qty_args1
    val qty_args3 = qty_args2 ~~ alpha_equivp_thms
  in
    fold_map (Quotient_Type.add_quotient_type {overloaded = false}) qty_args3 lthy
  end

(* a wrapper for lifting a raw constant *)
fun lift_raw_const qtys (qconst_name, rconst, mx', rsp_thm) lthy =
  let
    val rty = fastype_of rconst
    val qty = Quotient_Term.derive_qtyp lthy qtys rty
    val lhs_raw = Free (qconst_name, qty)
    val rhs_raw = rconst

    val raw_var = (Binding.name qconst_name, NONE, mx')
    val ((binding, _, mx), ctxt) = Proof_Context.cert_var raw_var lthy
    val lhs = Syntax.check_term ctxt lhs_raw
    val rhs = Syntax.check_term ctxt rhs_raw

    val (lhs_str, lhs_ty) = dest_Free lhs handle TERM _ => error "Constant already defined."
    val _ = if null (strip_abs_vars rhs) then () else error "The definiens cannot be an abstraction"
    val _ = if is_Const rhs then () else warning "The definiens is not a constant"

  in
    Quotient_Def.add_quotient_def (((binding, mx), Binding.empty_atts), (lhs, rhs)) rsp_thm  ctxt
  end


(* defines quotient constants *)
fun define_qconsts qtys consts_specs lthy =
  let
    val (qconst_infos, lthy') =
      fold_map (lift_raw_const qtys) consts_specs lthy
    val phi =
      Proof_Context.export_morphism lthy'
        (Proof_Context.transfer (Proof_Context.theory_of lthy') lthy)
  in
    (map (Quotient_Info.transform_quotconsts phi) qconst_infos, lthy')
  end


(* defines the quotient permutations and proves pt-class *)
fun define_qperms qtys qfull_ty_names tvs perm_specs raw_perm_laws lthy =
  let
    val lthy1 =
      lthy
      |> Local_Theory.exit_global
      |> Class.instantiation (qfull_ty_names, tvs, @{sort pt})

    val (_, lthy2) = define_qconsts qtys perm_specs lthy1

    val ((_, raw_perm_laws'), lthy3) = Variable.importT raw_perm_laws lthy2

    val lifted_perm_laws =
      map (Quotient_Tacs.lifted lthy3 qtys []) raw_perm_laws'
      |> Variable.exportT lthy3 lthy2

    fun tac ctxt =
      Class.intro_classes_tac ctxt [] THEN
        (ALLGOALS (resolve_tac ctxt lifted_perm_laws))
  in
    lthy2
    |> Class.prove_instantiation_exit tac
    |> Named_Target.theory_init
  end


(* defines the size functions and proves size-class *)
fun define_qsizes qtys qfull_ty_names tvs size_specs lthy =
  let
    fun tac ctxt = Class.intro_classes_tac ctxt []
  in
    lthy
    |> Local_Theory.exit_global
    |> Class.instantiation (qfull_ty_names, tvs, @{sort size})
    |> snd o (define_qconsts qtys size_specs)
    |> Class.prove_instantiation_exit tac
    |> Named_Target.theory_init
  end


(* lifts a theorem and cleans all "_raw" parts
   from variable names *)

local
  val any = Scan.one (Symbol.not_eof)
  val raw = Scan.this_string "_raw"
  val exclude =
    Scan.repeat (Scan.unless raw any) --| raw >> implode
  val parser = Scan.repeat (exclude || any)
in
  fun unraw_str s =
    s |> raw_explode
      |> Scan.finite Symbol.stopper parser >> implode
      |> fst
end

fun unraw_vars_thm ctxt thm =
  let
    fun unraw_var_str ((s, i), T) = ((unraw_str s, i), T)

    val vars = Term.add_vars (Thm.prop_of thm) []
    val vars' = map (Thm.cterm_of ctxt o Var o unraw_var_str) vars
  in
    Thm.instantiate ([], (vars ~~ vars')) thm
  end

fun unraw_bounds_thm th =
  let
    val trm = Thm.prop_of th
    val trm' = Term.map_abs_vars unraw_str trm
  in
    Thm.rename_boundvars trm trm' th
  end

fun lift_thms qtys simps thms ctxt =
  (map (Quotient_Tacs.lifted ctxt qtys simps
        #> unraw_bounds_thm
        #> unraw_vars_thm ctxt
        #> Drule.zero_var_indexes) thms, ctxt)



fun mk_supports_goal ctxt qtrm =
  let
    val vs = fresh_args ctxt qtrm
    val rhs = list_comb (qtrm, vs)
    val lhs = fold (curry HOLogic.mk_prod) vs @{term "()"}
      |> mk_supp
  in
    mk_supports lhs rhs
    |> HOLogic.mk_Trueprop
  end

fun supports_tac ctxt perm_simps =
  let
    val simpset1 =
      put_simpset HOL_basic_ss ctxt addsimps @{thms supports_def fresh_def[symmetric]}
    val simpset2 =
      put_simpset HOL_ss ctxt addsimps @{thms swap_fresh_fresh fresh_Pair}
  in
    EVERY' [ simp_tac simpset1,
             eqvt_tac ctxt (eqvt_strict_config addpres perm_simps),
             simp_tac simpset2 ]
  end

fun prove_supports_single ctxt perm_simps qtrm =
  let
    val goal = mk_supports_goal ctxt qtrm
    val ctxt' = Variable.auto_fixes goal ctxt
  in
    Goal.prove ctxt' [] [] goal
      (K (HEADGOAL (supports_tac ctxt perm_simps)))
    |> singleton (Proof_Context.export ctxt' ctxt)
  end

fun prove_supports ctxt perm_simps qtrms =
  map (prove_supports_single ctxt perm_simps) qtrms


(* finite supp lemmas for qtypes *)

fun prove_fsupp ctxt qtys qinduct qsupports_thms =
  let
    val (vs, ctxt') = Variable.variant_fixes (replicate (length qtys) "x") ctxt
    val goals = vs ~~ qtys
      |> map Free
      |> map (mk_finite o mk_supp)
      |> foldr1 (HOLogic.mk_conj)
      |> HOLogic.mk_Trueprop

    val tac =
      EVERY' [ resolve_tac ctxt' @{thms supports_finite},
               resolve_tac ctxt' qsupports_thms,
               asm_simp_tac (put_simpset HOL_ss ctxt'
                addsimps @{thms finite_supp supp_Pair finite_Un}) ]
  in
    Goal.prove ctxt' [] [] goals
      (K (HEADGOAL (resolve_tac ctxt' [qinduct] THEN_ALL_NEW tac)))
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> Old_Datatype_Aux.split_conj_thm
    |> map zero_var_indexes
  end


(* finite supp instances *)

fun fs_instance qtys qfull_ty_names tvs qfsupp_thms lthy =
  let
    val lthy1 =
      lthy
      |> Local_Theory.exit_global
      |> Class.instantiation (qfull_ty_names, tvs, @{sort fs})

    fun tac ctxt =
      Class.intro_classes_tac ctxt [] THEN
        (ALLGOALS (resolve_tac ctxt qfsupp_thms))
  in
    lthy1
    |> Class.prove_instantiation_exit tac
    |> Named_Target.theory_init
  end


(* proves that fv and fv_bn equals supp *)

fun gen_mk_goals fv supp =
  let
    val arg_ty =
      fastype_of fv
      |> domain_type
  in
    (arg_ty, fn x => HOLogic.mk_eq (fv $ x, supp x))
  end

fun mk_fvs_goals fv = gen_mk_goals fv mk_supp
fun mk_fv_bns_goals fv_bn alpha_bn = gen_mk_goals fv_bn (mk_supp_rel alpha_bn)

fun add_simpset ctxt thms = put_simpset HOL_basic_ss ctxt addsimps thms

fun symmetric thms =
  map (fn thm => thm RS @{thm sym}) thms

val supp_Abs_set = @{thms supp_Abs(1)[symmetric]}
val supp_Abs_res = @{thms supp_Abs(2)[symmetric]}
val supp_Abs_lst = @{thms supp_Abs(3)[symmetric]}

fun mk_supp_abs ctxt (BC (Set, _, _)) = EqSubst.eqsubst_tac ctxt [1] supp_Abs_set
  | mk_supp_abs ctxt (BC (Res, _, _)) = EqSubst.eqsubst_tac ctxt [1] supp_Abs_res
  | mk_supp_abs ctxt (BC (Lst, _, _)) = EqSubst.eqsubst_tac ctxt [1] supp_Abs_lst

fun mk_supp_abs_tac ctxt [] = []
  | mk_supp_abs_tac ctxt (BC (_, [], _)::xs) = mk_supp_abs_tac ctxt xs
  | mk_supp_abs_tac ctxt (bc::xs) = (DETERM o mk_supp_abs ctxt bc)::mk_supp_abs_tac ctxt xs

fun mk_bn_supp_abs_tac ctxt trm =
  trm
  |> fastype_of
  |> body_type
  |> (fn ty => case ty of
        @{typ "atom set"}  => simp_tac (add_simpset ctxt supp_Abs_set)
      | @{typ "atom list"} => simp_tac (add_simpset ctxt supp_Abs_lst)
      | _ => raise TERM ("mk_bn_supp_abs_tac", [trm]))


val thms1 = @{thms supp_Pair supp_eqvt[symmetric] Un_assoc conj_assoc}
val thms2 = @{thms de_Morgan_conj Collect_disj_eq finite_Un}
val thms3 = @{thms alphas prod_alpha_def prod_fv.simps rel_prod_conv permute_prod_def
  prod.rec prod.case prod.inject not_True_eq_False empty_def[symmetric] finite.emptyI}

fun prove_fv_supp qtys qtrms fvs fv_bns alpha_bns fv_simps eq_iffs perm_simps
  fv_bn_eqvts qinduct bclausess ctxt =
  let
    val goals1 = map mk_fvs_goals fvs
    val goals2 = map2 mk_fv_bns_goals fv_bns alpha_bns

    fun tac ctxt =
      SUBGOAL (fn (goal, i) =>
        let
          val (fv_fun, arg) =
            goal |> Envir.eta_contract
                 |> Logic.strip_assums_concl
                 |> HOLogic.dest_Trueprop
                 |> fst o HOLogic.dest_eq
                 |> dest_comb
          val supp_abs_tac =
            case (AList.lookup (op=) (qtrms ~~ bclausess) (head_of arg)) of
              SOME bclauses => EVERY' (mk_supp_abs_tac ctxt bclauses)
            | NONE => mk_bn_supp_abs_tac ctxt fv_fun
          val eqvt_rconfig = eqvt_relaxed_config addpres (perm_simps @ fv_bn_eqvts)
        in
          EVERY' [ TRY o asm_full_simp_tac (add_simpset ctxt (@{thm supp_Pair[symmetric]}::fv_simps)),
                   TRY o supp_abs_tac,
                   TRY o simp_tac (add_simpset ctxt @{thms supp_def supp_rel_def}),
                   TRY o eqvt_tac ctxt eqvt_rconfig,
                   TRY o simp_tac (add_simpset ctxt (@{thms Abs_eq_iff} @ eq_iffs)),
                   TRY o asm_full_simp_tac (add_simpset ctxt thms3),
                   TRY o simp_tac (add_simpset ctxt thms2),
                   TRY o asm_full_simp_tac (add_simpset ctxt (thms1 @ (symmetric fv_bn_eqvts)))] i
        end)
  in
    induct_prove qtys (goals1 @ goals2) qinduct tac ctxt
    |> map (atomize ctxt)
    |> map (simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms fun_eq_iff[symmetric]}))
  end


fun prove_bns_finite qtys qbns qinduct qbn_simps ctxt =
  let
    fun mk_goal qbn =
      let
        val arg_ty = domain_type (fastype_of qbn)
        val finite = @{term "finite :: atom set => bool"}
      in
        (arg_ty, fn x => finite $ (to_set (qbn $ x)))
      end

    val props = map mk_goal qbns
    val ss_tac = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps (qbn_simps @
      @{thms set_simps set_append finite_insert finite.emptyI finite_Un}))
  in
    induct_prove qtys props qinduct (K ss_tac) ctxt
  end


fun prove_perm_bn_alpha_thms qtys qperm_bns alpha_bns qinduct qperm_bn_simps qeq_iffs qalpha_refls ctxt =
  let
    val ([p], ctxt') = Variable.variant_fixes ["p"] ctxt
    val p = Free (p, @{typ perm})

    fun mk_goal qperm_bn alpha_bn =
      let
        val arg_ty = domain_type (fastype_of alpha_bn)
      in
        (arg_ty, fn x => (mk_id (Abs ("", arg_ty, alpha_bn $ Bound 0 $ (qperm_bn $ p $ Bound 0)))) $ x)
      end

    val props = map2 mk_goal qperm_bns alpha_bns
    val ss = @{thm id_def}::qperm_bn_simps @ qeq_iffs @ qalpha_refls
    val ss_tac = asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps ss)
  in
    induct_prove qtys props qinduct (K ss_tac) ctxt'
    |> Proof_Context.export ctxt' ctxt
    |> map (simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms id_def}))
  end

fun prove_permute_bn_thms qtys qbns qperm_bns qinduct qperm_bn_simps qbn_defs qbn_eqvts ctxt =
  let
    val ([p], ctxt') = Variable.variant_fixes ["p"] ctxt
    val p = Free (p, @{typ perm})

    fun mk_goal qbn qperm_bn =
      let
        val arg_ty = domain_type (fastype_of qbn)
      in
        (arg_ty, fn x =>
          (mk_id (Abs ("", arg_ty,
             HOLogic.mk_eq (mk_perm p (qbn $ Bound 0), qbn $ (qperm_bn $ p $ Bound 0)))) $ x))
      end

    val props = map2 mk_goal qbns qperm_bns
    val ss = @{thm id_def}::qperm_bn_simps @ qbn_defs
    val ss_tac =
      EVERY' [asm_full_simp_tac (put_simpset HOL_basic_ss ctxt' addsimps ss),
              TRY o eqvt_tac ctxt' (eqvt_strict_config addpres qbn_eqvts),
              TRY o asm_full_simp_tac (put_simpset HOL_basic_ss ctxt')]
  in
    induct_prove qtys props qinduct (K ss_tac) ctxt'
    |> Proof_Context.export ctxt' ctxt
    |> map (simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms id_def}))
  end



(*** proves strong exhauts theorems ***)

(* fixme: move into nominal_library *)
fun abs_const bmode ty =
  let
    val (const_name, binder_ty, abs_ty) =
      case bmode of
        Lst => (@{const_name "Abs_lst"}, @{typ "atom list"}, @{type_name abs_lst})
      | Set => (@{const_name "Abs_set"}, @{typ "atom set"},  @{type_name abs_set})
      | Res => (@{const_name "Abs_res"}, @{typ "atom set"},  @{type_name abs_res})
  in
    Const (const_name, [binder_ty, ty] ---> Type (abs_ty, [ty]))
  end

fun mk_abs bmode trm1 trm2 =
  abs_const bmode (fastype_of trm2) $ trm1 $ trm2

fun is_abs_eq thm =
  let
    fun is_abs trm =
      case (head_of trm) of
        Const (@{const_name "Abs_set"}, _) => true
      | Const (@{const_name "Abs_lst"}, _) => true
      | Const (@{const_name "Abs_res"}, _) => true
      | _ => false
  in
    thm |> Thm.prop_of
        |> HOLogic.dest_Trueprop
        |> HOLogic.dest_eq
        |> fst
        |> is_abs
  end


(* adds a freshness condition to the assumptions *)
fun mk_ecase_prems lthy c (params, prems, concl) bclauses =
  let
    val tys = map snd params
    val binders = get_all_binders bclauses

    fun prep_binder (opt, i) =
      let
        val t = Bound (length tys - i - 1)
      in
        case opt of
          NONE => setify_ty lthy (nth tys i) t
        | SOME bn => to_set_ty (fastype_of1 (tys, bn $ t)) (bn $ t)
      end

    val prems' =
      case binders of
        [] => prems                        (* case: no binders *)
      | _ => binders                       (* case: binders *)
          |> map prep_binder
          |> fold_union_env tys
          |> (fn t => mk_fresh_star t c)
          |> (fn t => HOLogic.mk_Trueprop t :: prems)
  in
    mk_full_horn params prems' concl
  end


(* derives the freshness theorem that there exists a p, such that
   (p o as) #* (c, t1,..., tn) *)
fun fresh_thm ctxt c parms binders bn_finite_thms =
  let
    fun prep_binder (opt, i) =
      case opt of
        NONE => setify ctxt (nth parms i)
      | SOME bn => to_set (bn $ (nth parms i))

    fun prep_binder2 (opt, i) =
      case opt of
        NONE => atomify ctxt (nth parms i)
      | SOME bn => bn $ (nth parms i)

    val rhs = HOLogic.mk_tuple ([c] @ parms @ (map prep_binder2 binders))
    val lhs = binders
      |> map prep_binder
      |> fold_union
      |> mk_perm (Bound 0)

    val goal = mk_fresh_star lhs rhs
      |> mk_exists ("p", @{typ perm})
      |> HOLogic.mk_Trueprop

    val ss = bn_finite_thms @ @{thms supp_Pair finite_supp finite_sets_supp}
      @ @{thms finite.intros finite_Un finite_set finite_fset}
  in
    Goal.prove ctxt [] [] goal
      (K (HEADGOAL (resolve_tac ctxt @{thms at_set_avoiding1}
          THEN_ALL_NEW (simp_tac (put_simpset HOL_ss ctxt addsimps ss)))))
  end


(* derives an abs_eq theorem of the form

   Exists q. [as].x = [p o as].(q o x)  for non-recursive binders
   Exists q. [as].x = [q o as].(q o x)  for recursive binders
*)
fun abs_eq_thm ctxt fprops p parms bn_eqvt permute_bns (bclause as (BC (bmode, binders, bodies))) =
  case binders of
    [] => []
  | _ =>
      let
        val rec_flag = is_recursive_binder bclause
        val binder_trm = comb_binders ctxt bmode parms binders
        val body_trm = foldl1 HOLogic.mk_prod (map (nth parms) bodies)

        val abs_lhs = mk_abs bmode binder_trm body_trm
        val abs_rhs =
          if rec_flag
          then mk_abs bmode (mk_perm (Bound 0) binder_trm) (mk_perm (Bound 0) body_trm)
          else mk_abs bmode (mk_perm p binder_trm) (mk_perm (Bound 0) body_trm)

        val abs_eq = HOLogic.mk_eq (abs_lhs, abs_rhs)
        val peq = HOLogic.mk_eq (mk_perm (Bound 0) binder_trm, mk_perm p binder_trm)

        val goal = HOLogic.mk_conj (abs_eq, peq)
          |> (fn t => HOLogic.mk_exists ("q", @{typ "perm"}, t))
          |> HOLogic.mk_Trueprop

        val ss = fprops @ @{thms set_simps set_append union_eqvt}
          @ @{thms fresh_star_Un fresh_star_Pair fresh_star_list fresh_star_singleton fresh_star_fset
          fresh_star_set}

        val tac1 =
          if rec_flag
          then resolve_tac ctxt @{thms Abs_rename_set' Abs_rename_res' Abs_rename_lst'}
          else resolve_tac ctxt @{thms Abs_rename_set  Abs_rename_res  Abs_rename_lst}

        val tac2 =
          EVERY' [simp_tac (put_simpset HOL_basic_ss ctxt addsimps ss),
            TRY o simp_tac (put_simpset HOL_ss ctxt)]
     in
       [ Goal.prove ctxt [] [] goal (K (HEADGOAL (tac1 THEN_ALL_NEW tac2)))
         |> (if rec_flag
             then eqvt_rule ctxt (eqvt_strict_config addpres bn_eqvt)
             else eqvt_rule ctxt (eqvt_strict_config addpres permute_bns)) ]
     end


val setify = @{lemma "xs = ys ==> set xs = set ys" by simp}

fun case_tac ctxt c bn_finite_thms eq_iff_thms bn_eqvt permute_bns perm_bn_alphas
  prems bclausess qexhaust_thm =
  let
    fun aux_tac prem bclauses =
      case (get_all_binders bclauses) of
        [] => EVERY' [resolve_tac ctxt [prem], assume_tac ctxt]
      | binders => Subgoal.SUBPROOF (fn {params, prems, concl, context = ctxt, ...} =>
          let
            val parms = map (Thm.term_of o snd) params
            val fthm = fresh_thm ctxt c parms binders bn_finite_thms

            val ss = @{thms fresh_star_Pair union_eqvt fresh_star_Un}
            val (([(_, fperm)], fprops), ctxt') = Obtain.result
              (fn ctxt' => EVERY1 [eresolve_tac ctxt [exE],
                            full_simp_tac (put_simpset HOL_basic_ss ctxt' addsimps ss),
                            REPEAT o (eresolve_tac ctxt @{thms conjE})]) [fthm] ctxt

            val abs_eq_thms = flat
             (map (abs_eq_thm ctxt' fprops (Thm.term_of fperm) parms bn_eqvt permute_bns) bclauses)

            val ((_, eqs), ctxt'') = Obtain.result
              (fn ctxt'' => EVERY1
                   [ REPEAT o (eresolve_tac ctxt @{thms exE}),
                     REPEAT o (eresolve_tac ctxt @{thms conjE}),
                     REPEAT o (dresolve_tac ctxt [setify]),
                     full_simp_tac (put_simpset HOL_basic_ss ctxt''
                      addsimps @{thms set_append set_simps})]) abs_eq_thms ctxt'

            val (abs_eqs, peqs) = split_filter is_abs_eq eqs

            val fprops' =
              map (eqvt_rule ctxt'' (eqvt_strict_config addpres permute_bns)) fprops
              @ map (eqvt_rule ctxt'' (eqvt_strict_config addpres bn_eqvt)) fprops

            (* for freshness conditions *)
            val tac1 = SOLVED' (EVERY'
              [ simp_tac (put_simpset HOL_basic_ss ctxt'' addsimps peqs),
                rewrite_goal_tac ctxt'' (@{thms fresh_star_Un[THEN eq_reflection]}),
                conj_tac ctxt'' (DETERM o resolve_tac ctxt'' fprops') ])

            (* for equalities between constructors *)
            val tac2 = SOLVED' (EVERY'
              [ resolve_tac ctxt [@{thm ssubst} OF prems],
                rewrite_goal_tac ctxt'' (map safe_mk_equiv eq_iff_thms),
                rewrite_goal_tac ctxt'' (map safe_mk_equiv abs_eqs),
                conj_tac ctxt'' (DETERM o resolve_tac ctxt'' (@{thms refl} @ perm_bn_alphas)) ])

            (* proves goal "P" *)
            val side_thm = Goal.prove ctxt'' [] [] (Thm.term_of concl)
              (K (EVERY1 [ resolve_tac ctxt'' [prem], RANGE [tac1, tac2] ]))
              |> singleton (Proof_Context.export ctxt'' ctxt)
          in
            resolve_tac ctxt [side_thm] 1
          end) ctxt
  in
    EVERY1 [resolve_tac ctxt [qexhaust_thm], RANGE (map2 aux_tac prems bclausess)]
  end


fun prove_strong_exhausts lthy exhausts bclausesss bn_finite_thms eq_iff_thms bn_eqvt permute_bns
  perm_bn_alphas =
  let
    val ((_, exhausts'), lthy') = Variable.import true exhausts lthy

    val ([c, a], lthy'') = Variable.variant_fixes ["c", "'a"] lthy'
    val c = Free (c, TFree (a, @{sort fs}))

    val (ecases, main_concls) = exhausts' (* ecases are of the form (params, prems, concl) *)
      |> map Thm.prop_of
      |> map Logic.strip_horn
      |> split_list

    val ecases' = (map o map) strip_full_horn ecases

    val premss = (map2 o map2) (mk_ecase_prems lthy'' c) ecases' bclausesss

    fun tac bclausess exhaust {prems, context} =
      case_tac context c bn_finite_thms eq_iff_thms bn_eqvt permute_bns perm_bn_alphas
        prems bclausess exhaust

    fun prove prems bclausess exhaust concl =
      Goal.prove lthy'' [] prems concl (tac bclausess exhaust)
  in
    map4 prove premss bclausesss exhausts' main_concls
    |> Proof_Context.export lthy'' lthy
  end



(** strong induction theorems **)

fun add_c_prop c c_ty trm =
  let
    val (P, arg) = dest_comb trm
    val (P_name, P_ty) = dest_Free P
    val (ty_args, bool) = strip_type P_ty
  in
    Free (P_name, (c_ty :: ty_args) ---> bool) $ c $ arg
  end

fun add_qnt_c_prop c_name c_ty trm =
  trm |> HOLogic.dest_Trueprop
      |> incr_boundvars 1
      |> add_c_prop (Bound 0) c_ty
      |> HOLogic.mk_Trueprop
      |> mk_all (c_name, c_ty)

fun prep_prem lthy c c_name c_ty bclauses (params, prems, concl) =
  let
    val tys = map snd params
    val binders = get_all_binders bclauses

    fun prep_binder (opt, i) =
      let
        val t = Bound (length tys - i - 1)
      in
        case opt of
          NONE => setify_ty lthy (nth tys i) t
        | SOME bn => to_set_ty (fastype_of1 (tys, bn $ t)) (bn $ t)
      end

    val prems' = prems
      |> map (incr_boundvars 1)
      |> map (add_qnt_c_prop c_name c_ty)

    val prems'' =
      case binders of
        [] => prems'                       (* case: no binders *)
      | _ => binders                       (* case: binders *)
          |> map prep_binder
          |> fold_union_env tys
          |> incr_boundvars 1
          |> (fn t => mk_fresh_star_ty c_ty t (Bound 0))
          |> (fn t => HOLogic.mk_Trueprop t :: prems')

    val concl' = concl
      |> HOLogic.dest_Trueprop
      |> incr_boundvars 1
      |> add_c_prop (Bound 0) c_ty
      |> HOLogic.mk_Trueprop
  in
    mk_full_horn (params @ [(c_name, c_ty)]) prems'' concl'
  end

fun prove_strong_induct lthy induct exhausts size_thms bclausesss =
  let
    val ((_, [induct']), lthy') = Variable.import true [induct] lthy

    val ([c_name, a], lthy'') = Variable.variant_fixes ["c", "'a"] lthy'
    val c_ty = TFree (a, @{sort fs})
    val c = Free (c_name, c_ty)

    val (prems, concl) = induct'
      |> Thm.prop_of
      |> Logic.strip_horn

    val concls = concl
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_conj
      |> map (add_c_prop c c_ty)
      |> map HOLogic.mk_Trueprop

    val prems' = prems
      |> map strip_full_horn
      |> map2 (prep_prem lthy'' c c_name c_ty) (flat bclausesss)

    fun pat_tac ctxt thm =
      Subgoal.FOCUS (fn {params, context = ctxt', ...} =>
        let
          val ty_parms = map (fn (_, ct) => (fastype_of (Thm.term_of ct), ct)) params
          val vs = Term.add_vars (Thm.prop_of thm) []
          val vs_tys = map (Type.legacy_freeze_type o snd) vs
          val assigns = map (lookup ty_parms) vs_tys
          val thm' = infer_instantiate ctxt' (map #1 vs ~~ assigns) thm
        in
          resolve_tac ctxt' [thm'] 1
        end) ctxt
      THEN_ALL_NEW asm_full_simp_tac (put_simpset HOL_basic_ss ctxt)

    fun size_simp_tac ctxt =
      simp_tac (put_simpset size_ss ctxt addsimps (@{thms comp_def snd_conv} @ size_thms))
  in
    Goal.prove_common lthy'' NONE [] prems' concls
      (fn {prems, context = ctxt} =>
        Induction_Schema.induction_schema_tac ctxt prems
        THEN RANGE (map (pat_tac ctxt) exhausts) 1
        THEN prove_termination_ind ctxt 1
        THEN ALLGOALS (size_simp_tac ctxt))
    |> Proof_Context.export lthy'' lthy
  end


end (* structure *)
