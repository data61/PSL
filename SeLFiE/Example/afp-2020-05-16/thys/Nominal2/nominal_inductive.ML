(*  Title:      nominal_inductive.ML
    Author:     Christian Urban
    Author:     Tjark Weber

    Infrastructure for proving strong induction theorems
    for inductive predicates involving nominal datatypes.

    Code based on an earlier version by Stefan Berghofer.
*)

signature NOMINAL_INDUCTIVE =
sig
  val prove_strong_inductive: string list -> string list -> term list list -> thm -> thm list ->
    Proof.context -> Proof.state
  val prove_strong_inductive_cmd: xstring * (string * string list) list -> Proof.context -> Proof.state
end

structure Nominal_Inductive : NOMINAL_INDUCTIVE =
struct

fun mk_cplus p q =
  Thm.apply (Thm.apply @{cterm "plus :: perm => perm => perm"} p) q

fun mk_cminus p =
  Thm.apply @{cterm "uminus :: perm => perm"} p

fun minus_permute_intro_tac ctxt p =
  resolve_tac ctxt [Thm.instantiate' [] [SOME (mk_cminus p)] @{thm permute_boolE}]

fun minus_permute_elim p thm =
  thm RS (Thm.instantiate' [] [NONE, SOME (mk_cminus p)] @{thm permute_boolI})

(* fixme: move to nominal_library *)
fun real_head_of (@{term Trueprop} $ t) = real_head_of t
  | real_head_of (Const (@{const_name Pure.imp}, _) $ _ $ t) = real_head_of t
  | real_head_of (Const (@{const_name Pure.all}, _) $ Abs (_, _, t)) = real_head_of t
  | real_head_of (Const (@{const_name All}, _) $ Abs (_, _, t)) = real_head_of t
  | real_head_of (Const (@{const_name HOL.induct_forall}, _) $ Abs (_, _, t)) = real_head_of t
  | real_head_of t = head_of t


fun mk_vc_compat (avoid, avoid_trm) prems concl_args params =
  if null avoid then
    []
  else
    let
      val vc_goal = concl_args
        |> HOLogic.mk_tuple
        |> mk_fresh_star avoid_trm
        |> HOLogic.mk_Trueprop
        |> (curry Logic.list_implies) prems
        |> fold_rev (Logic.all o Free) params
      val finite_goal = avoid_trm
        |> mk_finite
        |> HOLogic.mk_Trueprop
        |> (curry Logic.list_implies) prems
        |> fold_rev (Logic.all o Free) params
    in
      [vc_goal, finite_goal]
    end

(* fixme: move to nominal_library *)
fun map_term prop f trm =
  if prop trm
  then f trm
  else case trm of
    (t1 $ t2) => map_term prop f t1 $ map_term prop f t2
  | Abs (x, T, t) => Abs (x, T, map_term prop f t)
  | _ => trm

fun add_p_c p (c, c_ty) trm =
  let
    val (P, args) = strip_comb trm
    val (P_name, P_ty) = dest_Free P
    val (ty_args, bool) = strip_type P_ty
    val args' = map (mk_perm p) args
  in
    list_comb (Free (P_name, (c_ty :: ty_args) ---> bool),  c :: args')
    |> (fn t => HOLogic.all_const c_ty $ lambda c t )
    |> (fn t => HOLogic.all_const @{typ perm} $  lambda p t)
  end

fun induct_forall_const T =
  Const (@{const_name HOL.induct_forall}, (T --> @{typ bool}) --> @{typ bool})

fun mk_induct_forall (a, T) t =
  induct_forall_const T $ Abs (a, T, t)

fun add_c_prop qnt Ps (c, c_name, c_ty) trm =
  let
    fun add t =
      let
        val (P, args) = strip_comb t
        val (P_name, P_ty) = dest_Free P
        val (ty_args, bool) = strip_type P_ty
        val args' = args
          |> qnt ? map (incr_boundvars 1)
      in
        list_comb (Free (P_name, (c_ty :: ty_args) ---> bool), c :: args')
          |> qnt ? mk_induct_forall (c_name, c_ty)
      end
  in
    map_term (member (op =) Ps o head_of) add trm
  end

fun prep_prem Ps c_name c_ty (avoid, avoid_trm) (params, prems, concl) =
  let
    val prems' = prems
      |> map (incr_boundvars 1)
      |> map (add_c_prop true Ps (Bound 0, c_name, c_ty))

    val avoid_trm' = avoid_trm
      |> fold_rev absfree (params @ [(c_name, c_ty)])
      |> strip_abs_body
      |> (fn t => mk_fresh_star_ty c_ty t (Bound 0))
      |> HOLogic.mk_Trueprop

    val prems'' =
      if null avoid
      then prems'
      else avoid_trm' :: prems'

    val concl' = concl
      |> incr_boundvars 1
      |> add_c_prop false Ps (Bound 0, c_name, c_ty)
  in
    mk_full_horn (params @ [(c_name, c_ty)]) prems'' concl'
  end

(* fixme: move to nominal_library *)
fun same_name (Free (a1, _), Free (a2, _)) = (a1 = a2)
  | same_name (Var (a1, _), Var (a2, _)) = (a1 = a2)
  | same_name (Const (a1, _), Const (a2, _)) = (a1 = a2)
  | same_name _ = false

(* fixme: move to nominal_library *)
fun map7 _ [] [] [] [] [] [] [] = []
  | map7 f (x :: xs) (y :: ys) (z :: zs) (u :: us) (v :: vs) (r :: rs) (s :: ss) =
      f x y z u v r s :: map7 f xs ys zs us vs rs ss

(* local abbreviations *)

local
  open Nominal_Permeq
in

  (* by default eqvt_strict_config contains unwanted @{thm permute_pure} *)

  val eqvt_sconfig = eqvt_strict_config addpres @{thms permute_minus_cancel}

  fun eqvt_stac ctxt = eqvt_tac ctxt eqvt_sconfig
  fun eqvt_srule ctxt = eqvt_rule ctxt eqvt_sconfig

end

val all_elims =
  let
    fun spec' ct =
      Thm.instantiate' [SOME (Thm.ctyp_of_cterm ct)] [NONE, SOME ct] @{thm spec}
  in
    fold (fn ct => fn th => th RS spec' ct)
  end

fun helper_tac flag prm p ctxt =
  Subgoal.SUBPROOF (fn {context = ctxt', prems, ...} =>
    let
      val prems' = prems
        |> map (minus_permute_elim p)
        |> map (eqvt_srule ctxt')

      val prm' = (prems' MRS prm)
        |> flag ? (all_elims [p])
        |> flag ? (eqvt_srule ctxt')
    in
      asm_full_simp_tac (put_simpset HOL_ss ctxt' addsimps (prm' :: @{thms HOL.induct_forall_def})) 1
    end) ctxt

fun non_binder_tac prem intr_cvars Ps ctxt =
  Subgoal.SUBPROOF (fn {context = ctxt', params, prems, ...} =>
    let
      val (prms, p, _) = split_last2 (map snd params)
      val prm_tys = map (fastype_of o Thm.term_of) prms
      val cperms = map (Thm.cterm_of ctxt' o perm_const) prm_tys
      val p_prms = map2 (fn ct1 => fn ct2 => Thm.mk_binop ct1 p ct2) cperms prms
      val prem' = prem
        |> infer_instantiate ctxt' (map (#1 o dest_Var o Thm.term_of) intr_cvars ~~ p_prms)
        |> eqvt_srule ctxt'

      (* for inductive-premises*)
      fun tac1 prm = helper_tac true prm p ctxt'

      (* for non-inductive premises *)
      fun tac2 prm =
        EVERY' [ minus_permute_intro_tac ctxt' p,
                 eqvt_stac ctxt',
                 helper_tac false prm p ctxt' ]

      fun select prm (t, i) =
        (if member same_name Ps (real_head_of t) then tac1 prm else tac2 prm) i
    in
      EVERY1 [ eqvt_stac ctxt',
               resolve_tac ctxt' [prem'],
               RANGE (map (SUBGOAL o select) prems) ]
    end) ctxt

fun fresh_thm ctxt user_thm p c concl_args avoid_trm =
  let
    val conj1 =
      mk_fresh_star (mk_perm (Bound 0) (mk_perm p avoid_trm)) c
    val conj2 =
      mk_fresh_star_ty @{typ perm} (mk_supp (HOLogic.mk_tuple (map (mk_perm p) concl_args))) (Bound 0)
    val fresh_goal = mk_exists ("q", @{typ perm}) (HOLogic.mk_conj (conj1, conj2))
      |> HOLogic.mk_Trueprop

    val ss = @{thms finite_supp supp_Pair finite_Un permute_finite} @
             @{thms fresh_star_Pair fresh_star_permute_iff}
    val simp = asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps ss)
  in
    Goal.prove ctxt [] [] fresh_goal
      (K (HEADGOAL (resolve_tac ctxt @{thms at_set_avoiding2}
          THEN_ALL_NEW EVERY' [cut_facts_tac user_thm, REPEAT o
            eresolve_tac ctxt @{thms conjE}, simp])))
  end

val supp_perm_eq' = @{lemma "fresh_star (supp (permute p x)) q ==> permute p x == permute (q + p) x"
  by (simp add: supp_perm_eq)}

val fresh_star_plus = @{lemma "fresh_star (permute q (permute p x)) c ==> fresh_star (permute (q + p) x) c"
  by (simp add: permute_plus)}


fun binder_tac prem intr_cvars param_trms Ps user_thm avoid_trm concl_args ctxt =
  Subgoal.FOCUS (fn {context = ctxt, params, prems, concl, ...} =>
    let
      val (prms, p, c) = split_last2 (map snd params)
      val prm_trms = map Thm.term_of prms
      val prm_tys = map fastype_of prm_trms

      val avoid_trm' = subst_free (param_trms ~~ prm_trms) avoid_trm
      val concl_args' = map (subst_free (param_trms ~~ prm_trms)) concl_args

      val user_thm' = map (infer_instantiate ctxt (map (#1 o dest_Var o Thm.term_of) intr_cvars ~~ prms)) user_thm
        |> map (full_simplify (put_simpset HOL_ss ctxt addsimps (@{thm fresh_star_Pair}::prems)))

      val fthm = fresh_thm ctxt user_thm' (Thm.term_of p) (Thm.term_of c) concl_args' avoid_trm'

      val (([(_, q)], fprop :: fresh_eqs), ctxt') = Obtain.result
              (K (EVERY1 [eresolve_tac ctxt @{thms exE},
                          full_simp_tac (put_simpset HOL_basic_ss ctxt
                            addsimps @{thms supp_Pair fresh_star_Un}),
                          REPEAT o eresolve_tac ctxt @{thms conjE},
                          dresolve_tac ctxt [fresh_star_plus],
                          REPEAT o dresolve_tac ctxt [supp_perm_eq']])) [fthm] ctxt

      val expand_conv = Conv.try_conv (Conv.rewrs_conv fresh_eqs)
      fun expand_conv_bot ctxt = Conv.bottom_conv (K expand_conv) ctxt

      val cperms = map (Thm.cterm_of ctxt' o perm_const) prm_tys
      val qp_prms = map2 (fn ct1 => fn ct2 => Thm.mk_binop ct1 (mk_cplus q p) ct2) cperms prms
      val prem' = prem
        |> infer_instantiate ctxt' (map (#1 o dest_Var o Thm.term_of) intr_cvars ~~ qp_prms)
        |> eqvt_srule ctxt'

      val fprop' = eqvt_srule ctxt' fprop
      val tac_fresh = simp_tac (put_simpset HOL_basic_ss ctxt' addsimps [fprop'])

      (* for inductive-premises*)
      fun tac1 prm = helper_tac true prm (mk_cplus q p) ctxt'

      (* for non-inductive premises *)
      fun tac2 prm =
        EVERY' [ minus_permute_intro_tac ctxt' (mk_cplus q p),
                 eqvt_stac ctxt',
                 helper_tac false prm (mk_cplus q p) ctxt' ]

      fun select prm (t, i) =
        (if member same_name Ps (real_head_of t) then tac1 prm else tac2 prm) i

      val side_thm = Goal.prove ctxt' [] [] (Thm.term_of concl)
        (fn {context = ctxt'', ...} =>
           EVERY1 [ CONVERSION (expand_conv_bot ctxt''),
                    eqvt_stac ctxt'',
                    resolve_tac ctxt'' [prem'],
                    RANGE (tac_fresh :: map (SUBGOAL o select) prems) ])
        |> singleton (Proof_Context.export ctxt' ctxt)
    in
      resolve_tac ctxt [side_thm] 1
    end) ctxt

fun case_tac ctxt Ps avoid avoid_trm intr_cvars param_trms prem user_thm concl_args =
  let
    val tac1 = non_binder_tac prem intr_cvars Ps ctxt
    val tac2 = binder_tac prem intr_cvars param_trms Ps user_thm avoid_trm concl_args ctxt
  in
    EVERY' [ resolve_tac ctxt @{thms allI}, resolve_tac ctxt @{thms allI},
             if null avoid then tac1 else tac2 ]
  end

fun prove_sinduct_tac raw_induct user_thms Ps avoids avoid_trms intr_cvars param_trms concl_args
  {prems, context = ctxt} =
  let
    val cases_tac =
      map7 (case_tac ctxt Ps) avoids avoid_trms intr_cvars param_trms prems user_thms concl_args
  in
    EVERY1 [ DETERM o resolve_tac ctxt [raw_induct], RANGE cases_tac ]
  end

val normalise = @{lemma "(Q \<longrightarrow> (\<forall>p c. P p c)) \<Longrightarrow> (\<And>c. Q \<Longrightarrow> P (0::perm) c)" by simp}

fun prove_strong_inductive pred_names rule_names avoids raw_induct intrs ctxt =
  let
    val ((_, [raw_induct']), ctxt') = Variable.import true [raw_induct] ctxt

    val (ind_prems, ind_concl) = raw_induct'
      |> Thm.prop_of
      |> Logic.strip_horn
      |>> map strip_full_horn
    val params = map (fn (x, _, _) => x) ind_prems
    val param_trms = (map o map) Free params

    val intr_vars_tys = map (fn t => rev (Term.add_vars (Thm.prop_of t) [])) intrs
    val intr_vars = (map o map) fst intr_vars_tys
    val intr_vars_substs = map2 (curry (op ~~)) intr_vars param_trms
    val intr_cvars = (map o map) (Thm.cterm_of ctxt o Var) intr_vars_tys

    val (intr_prems, intr_concls) = intrs
      |> map Thm.prop_of
      |> map2 subst_Vars intr_vars_substs
      |> map Logic.strip_horn
      |> split_list

    val intr_concls_args =
      map (snd o fixed_nonfixed_args ctxt' o HOLogic.dest_Trueprop) intr_concls

    val avoid_trms = avoids
      |> (map o map) (setify ctxt')
      |> map fold_union

    val vc_compat_goals =
      map4 mk_vc_compat (avoids ~~ avoid_trms) intr_prems intr_concls_args params

    val ([c_name, a, p], ctxt'') = Variable.variant_fixes ["c", "'a", "p"] ctxt'
    val c_ty = TFree (a, @{sort fs})
    val c = Free (c_name, c_ty)
    val p = Free (p, @{typ perm})

    val (preconds, ind_concls) = ind_concl
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_conj
      |> map HOLogic.dest_imp
      |> split_list

    val Ps = map (fst o strip_comb) ind_concls

    val ind_concl' = ind_concls
      |> map (add_p_c p (c, c_ty))
      |> (curry (op ~~)) preconds
      |> map HOLogic.mk_imp
      |> fold_conj
      |> HOLogic.mk_Trueprop

    val ind_prems' = ind_prems
      |> map2 (prep_prem Ps c_name c_ty) (avoids ~~ avoid_trms)

    fun after_qed ctxt_outside user_thms ctxt =
      let
        val strong_ind_thms = Goal.prove ctxt [] ind_prems' ind_concl'
        (prove_sinduct_tac raw_induct user_thms Ps avoids avoid_trms intr_cvars param_trms intr_concls_args)
          |> singleton (Proof_Context.export ctxt ctxt_outside)
          |> Old_Datatype_Aux.split_conj_thm
          |> map (fn thm => thm RS normalise)
          |> map (asm_full_simplify (put_simpset HOL_basic_ss ctxt
              addsimps @{thms permute_zero induct_rulify}))
          |> map (Drule.rotate_prems (length ind_prems'))
          |> map zero_var_indexes

        val qualified_thm_name = pred_names
          |> map Long_Name.base_name
          |> space_implode "_"
          |> (fn s => Binding.qualify false s (Binding.name "strong_induct"))

        val attrs =
          [ Attrib.internal (K (Rule_Cases.consumes 1)),
            Attrib.internal (K (Rule_Cases.case_names rule_names)) ]
      in
        ctxt
        |> Local_Theory.note ((qualified_thm_name, attrs), strong_ind_thms)
        |> snd
      end
  in
    Proof.theorem NONE (after_qed ctxt) ((map o map) (rpair []) vc_compat_goals) ctxt''
  end

fun prove_strong_inductive_cmd (pred_name, avoids) ctxt =
  let
    val ({names, ...}, {raw_induct, intrs, ...}) =
      Inductive.the_inductive_global ctxt (long_name ctxt pred_name)

    val rule_names = hd names
      |> the o Induct.lookup_inductP ctxt
      |> fst o Rule_Cases.get
      |> map (fst o fst)

    val case_names = map fst avoids
    val _ = case duplicates (op =) case_names of
        [] => ()
      | xs => error ("Duplicate case names: " ^ commas_quote xs)
    val _ = case subtract (op =) rule_names case_names of
        [] => ()
      | xs => error ("No such case(s) in inductive definition: " ^ commas_quote xs)

    val avoids_ordered = order_default (op =) [] rule_names avoids

    fun read_avoids avoid_trms intr =
      let
        (* fixme hack *)
        val (((_, ctrms), _), ctxt') = Variable.import true [intr] ctxt
        val trms = map (Thm.term_of o snd) ctrms
        val ctxt'' = fold Variable.declare_term trms ctxt'
      in
        map (Syntax.read_term ctxt'') avoid_trms
      end

    val avoid_trms = map2 read_avoids avoids_ordered intrs
  in
    prove_strong_inductive names rule_names avoid_trms raw_induct intrs ctxt
  end

(* outer syntax *)
local
  val single_avoid_parser =
    Parse.name -- (@{keyword ":"} |-- Parse.and_list1 Parse.term)

  val avoids_parser =
    Scan.optional (@{keyword "avoids"} |-- Parse.enum1 "|" single_avoid_parser) []

  val main_parser = Parse.name -- avoids_parser
in
  val _ =
    Outer_Syntax.local_theory_to_proof @{command_keyword nominal_inductive}
      "prove strong induction theorem for inductive predicate involving nominal datatypes"
        (main_parser >> prove_strong_inductive_cmd)
end

end
