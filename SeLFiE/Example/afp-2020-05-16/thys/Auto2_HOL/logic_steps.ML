(*
  File: logic_steps.ML
  Author: Bohua Zhan

  Core (logic) proofsteps.
*)

signature LOGIC_PROOFSTEPS =
sig
  (* General logic *)
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep

  val exists_elim_prfstep: proofstep
  val add_logic_proofsteps: theory -> theory

  val mk_all_disj: term list * term list -> term
  val strip_all_disj: term -> term list * term list
  val norm_all_disj: Proof.context -> conv
  val replace_disj_vars:
      Proof.context -> term list * term list -> term list * term list
  val disj_prop_match:
      Proof.context -> id_inst ->
      term * (term list * term list) * ((indexname * typ) list * cterm list) ->
      id_inst_th list
  val norm_conj: conv

  (* DISJ items. *)
  val TY_DISJ: string
  val disj_to_ritems: bool -> term -> thm -> raw_item list
  val disj_to_update: bool -> term -> box_id * int option * thm -> raw_update
  val dest_tname_of_disj: cterm list -> term * cterm list
  val is_match_prem_only: box_item -> bool
  val analyze_disj_th: Proof.context -> thm -> term * thm
  val disj_rewr_terms: term list -> term list
  val output_disj_fn: item_output
  val disj_prop_matcher: item_matcher

  val reduce_disj_True: conv
  val match_update_prfstep: proofstep
  val match_one_sch_prfstep: proofstep
  val disj_match_iff_prfstep: proofstep
  val disj_create_case_prfstep: proofstep
  val disj_shadow_prfstep: proofstep
  val add_disj_proofsteps: theory -> theory

  (* Normalizers *)
  val split_not_imp_th: thm -> thm list
  val split_conj_gen_th: Proof.context -> thm -> thm list
  val eq_normalizer: normalizer
  val property_normalizer: normalizer
  val disj_normalizer: normalizer
  val logic_thm_update: Proof.context -> box_id * thm -> raw_update
  val add_disj_normalizers: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

fun boolVar s = Var ((s, 0), boolT)

(* Shadowing based on equivalence. For both PROP and TERM items,
   shadowing is based on subterm equivalence, skipping any Not (~) at
   head.
 *)
fun shadow_item_fn ctxt item1 item2 =
    if #sc item1 = 0 andalso #sc item2 = 0 then []
    else let
      val id = BoxItem.merged_id ctxt [item1, item2]
      val _ = assert (forall (BoxItem.match_ty_strs [TY_TERM, TY_PROP])
                             [item1, item2])
                     "shadow_item_fn"
      val (tname1, tname2) =
          (the_single (#tname item1), the_single (#tname item2))
          handle List.Empty => raise Fail "shadow_item_fn"
      val (t1, t2) = (Thm.term_of tname1, Thm.term_of tname2)

      val (lhs, rhs) =
          if fastype_of t1 = boolT andalso is_neg t1 andalso
             fastype_of t2 = boolT andalso is_neg t2 then
            (UtilLogic.get_cneg tname1, UtilLogic.get_cneg tname2)
          else
            (tname1, tname2)

      val equiv_ids =
          (RewriteTable.subequiv_info ctxt id (lhs, rhs))
              |> map fst |> filter BoxID.has_incr_id
              |> Util.max_partial (BoxID.is_eq_ancestor ctxt)

      val item_to_shadow =
          if #uid item1 > #uid item2 then item1 else item2
      fun process_id id' =
          ShadowItem {id = id', item = item_to_shadow}
    in
      map process_id equiv_ids
    end

val shadow_prop_item =
    {name = "shadow_prop",
     args = [TypedUniv TY_PROP, TypedUniv TY_PROP],
     func = TwoStep shadow_item_fn}

val shadow_term_item =
    {name = "shadow_term",
     args = [TypedUniv TY_TERM, TypedUniv TY_TERM],
     func = TwoStep shadow_item_fn}

fun eq_abs_fn ctxt item1 item2 =
    let
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val id = BoxID.merge_boxes ctxt (id1, id2)
      val (ct1, ct2) = apply2 the_single (tname1, tname2)
      val (t1, t2) = apply2 Thm.term_of (ct1, ct2)
    in
      if not (Util.is_abs t1) orelse not (Util.is_abs t2) then []
      else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
      else if Term_Ord.term_ord (t2, t1) = LESS then []
      else let
        fun process_equiv (id', eq_th) =
            let
              val (lhs, rhs) = (Util.lhs_of eq_th, Util.rhs_of eq_th)
            in
              AddItems {id = id', sc = SOME 1,
                        raw_items = [Fact (TY_EQ, [lhs, rhs], eq_th)]}
            end
      in
        (Matcher.rewrite_match ctxt (t1, ct2) (id, fo_init))
            |> map (fn ((id, _), eq_th) => (id, eq_th))
            |> filter (BoxID.has_incr_id o fst)
            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            |> map process_equiv
      end
    end

val eq_abs_prfstep =
    {name = "eq_abs",
     args = [TypedUniv TY_TERM, TypedUniv TY_TERM],
     func = TwoStep eq_abs_fn}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context. We produce at most two variables at a
   time.
 *)
fun exists_elim_fn ctxt {id, prop, ...} =
    if not (BoxID.has_incr_id id) then [] else
    let
      val t = prop_of' prop
    in
      if is_ex t orelse is_bex t orelse
         (is_neg t andalso is_obj_all (dest_not t)) orelse
         (is_neg t andalso is_ball (dest_not t)) then
        let
          val (ritems, th') =
              prop |> apply_to_thm' (UtilLogic.normalize_exists ctxt)
                   |> Update.apply_exists_ritems ctxt
        in
          [AddItems {id = id, sc = NONE,
                     raw_items = ritems @ [Update.thm_to_ritem th']}]
        end
      else []
    end

val exists_elim_prfstep =
    {name = "exists_elim",
     args = [TypedUniv TY_PROP],
     func = OneStep exists_elim_fn}

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item, exists_elim_prfstep, eq_abs_prfstep
    ]

(* Given (x_1 ... x_n, A_1 ... A_n), create the corresponding
   forall-disj term.
 *)
fun mk_all_disj (vars, terms) =
    case vars of
        [] => list_disj terms
      | var :: vars' => mk_obj_all var (mk_all_disj (vars', terms))

(* Normalize t into a disjunction of terms. *)
fun strip_disj t =
    if is_disj t then
      maps strip_disj [dest_arg1 t, dest_arg t]
    else if is_imp t then
      maps strip_disj [get_neg (dest_arg1 t), dest_arg t]
    else if is_neg t then
      let
        val t' = dest_not t
      in
        if is_neg t' then strip_disj (dest_not t')
        else if is_conj t' then
          maps strip_disj [get_neg (dest_arg1 t'), get_neg (dest_arg t')]
        else [t]
      end
    else [t]

(* Normalize a term into the form !x_1 ... x_n. A_1 | ... | A_n *)
fun strip_all_disj t =
    if is_obj_all t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, disjs) = strip_all_disj body
          in
            if exists (Util.occurs_free var) disjs then (var :: vars, disjs)
            else (vars, disjs)
          end
        | f $ arg => strip_all_disj (f $ UtilLogic.force_abs_form arg)
        | _ => raise Fail "strip_all_disj"
    else if is_ball t then
      case t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, disjs) = strip_all_disj body
          in
            (var :: vars, get_neg mem :: disjs)
          end
        | f $ S $ arg => strip_all_disj (f $ S $ UtilLogic.force_abs_form arg)
        | _ => raise Fail "strip_all_disj"
    else if is_neg t andalso is_ex (dest_not t) then
      case dest_not t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, disjs) = strip_all_disj (get_neg body)
          in
            if exists (Util.occurs_free var) disjs then (var :: vars, disjs)
            else (vars, disjs)
          end
        | f $ arg => strip_all_disj (get_neg (f $ UtilLogic.force_abs_form arg))
        | _ => raise Fail "strip_all_disj"
    else if is_neg t andalso is_bex (dest_not t) then
      case dest_not t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, disjs) = strip_all_disj (get_neg body)
          in
            (var :: vars, get_neg mem :: disjs)
          end
        | f $ S $ arg => strip_all_disj (get_neg (f $ S $ UtilLogic.force_abs_form arg))
        | _ => raise Fail "strip_all_disj"
    else if is_disj t then
      let
        val (v1, ts1) = strip_all_disj (dest_arg1 t)
        val (v2, ts2) = strip_all_disj (dest_arg t)
      in
        (v1 @ v2, ts1 @ ts2)
      end
    else if is_imp t then
      let
        val (v1, ts1) = strip_all_disj (get_neg (dest_arg1 t))
        val (v2, ts2) = strip_all_disj (dest_arg t)
      in
        (v1 @ v2, ts1 @ ts2)
      end
    else if is_neg t then
      let
        val t' = dest_not t
      in
        if is_neg t' then strip_all_disj (dest_not t')
        else if is_conj t' then
          let
            val (v1, ts1) = strip_all_disj (get_neg (dest_arg1 t'))
            val (v2, ts2) = strip_all_disj (get_neg (dest_arg t'))
          in
            (v1 @ v2, ts1 @ ts2)
          end
        else ([], [t])
      end
    else ([], [t])

(* Normalize (A_1 | A_2 | ... | A_m) | (B_1 | B_2 | ... | B_n) *)
fun norm_disj_clauses ct =
    let
      val (arg1, _) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_disj arg1 then
        Conv.every_conv [rewr_obj_eq UtilBase.disj_assoc_th,
                         Conv.arg_conv norm_disj_clauses] ct
      else
        Conv.all_conv ct
    end

(* Normalize ct. *)
fun norm_disj ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "norm_disj: wrong type"
    in
      if is_disj t then
        Conv.every_conv [Conv.binop_conv norm_disj, norm_disj_clauses] ct
      else if is_imp t then
        Conv.every_conv [rewr_obj_eq UtilBase.imp_conv_disj_th, norm_disj] ct
      else if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th, norm_disj] ct
      else if is_neg t andalso is_conj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_conj_th, norm_disj] ct
      else
        Conv.all_conv ct
    end

(* Normalize to forall at the top-level *)
fun norm_all_disj ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_obj_all t then
        if not (Util.is_subterm (Bound 0) (dest_arg t)) then
          Conv.every_conv [rewr_obj_eq UtilBase.all_trivial_th,
                           norm_all_disj ctxt] ct
        else
          Conv.every_conv [Conv.binder_conv (norm_all_disj o snd) ctxt] ct
      else if is_ball t then
        Conv.every_conv [rewr_obj_eq UtilBase.Ball_def_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_ex (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.not_ex_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_bex (dest_not t) then
        Conv.every_conv [
          Conv.arg_conv (rewr_obj_eq UtilBase.Bex_def_th), norm_all_disj ctxt] ct
      else if is_disj t then
        let
          val eq1 = Conv.binop_conv (norm_all_disj ctxt) ct
          val rhs = Util.rhs_of eq1
        in
          if is_obj_all (dest_arg1 rhs) then
            Conv.every_conv [Conv.rewr_conv eq1,
                             rewr_obj_eq UtilBase.disj_commute_th,
                             rewr_obj_eq UtilBase.swap_all_disj_th,
                             norm_all_disj ctxt] ct
          else if is_obj_all (dest_arg rhs) then
            Conv.every_conv [Conv.rewr_conv eq1,
                             rewr_obj_eq UtilBase.swap_all_disj_th,
                             norm_all_disj ctxt] ct
          else
            Conv.every_conv [Conv.rewr_conv eq1, norm_disj_clauses] ct
        end
      else if is_imp t then
        Conv.every_conv [rewr_obj_eq UtilBase.imp_conv_disj_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_conj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_conj_th, norm_all_disj ctxt] ct
      else
        Conv.all_conv ct
    end

fun mk_disj_eq eq_ths =
    case eq_ths of
        [] => raise Fail "mk_disj_eq"
      | [eq] => eq
      | eq :: eqs' => Drule.binop_cong_rule UtilBase.cDisj eq (mk_disj_eq eqs')

(* Sort A | (B_1 | B_2 | ... | B_n), assuming the right side is sorted. *)
fun sort_disj_clause_aux ct =
    if not (is_disj (Thm.term_of ct)) then Conv.all_conv ct else
    let
      val (arg1, arg2) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_disj arg2 then
        if Term_Ord.term_ord (dest_arg1 arg2, arg1) = LESS then
          Conv.every_conv [rewr_obj_eq (obj_sym UtilBase.disj_assoc_th),
                           Conv.arg1_conv (rewr_obj_eq UtilBase.disj_commute_th),
                           rewr_obj_eq UtilBase.disj_assoc_th,
                           Conv.arg_conv sort_disj_clause_aux] ct
        else
          Conv.all_conv ct
      else
        if Term_Ord.term_ord (arg2, arg1) = LESS then
          rewr_obj_eq (obj_sym UtilBase.disj_commute_th) ct
        else
          Conv.all_conv ct
    end

(* Sort A_1 | ... | A_n. *)
fun sort_disj_clause ct =
    if not (is_disj (Thm.term_of ct)) then Conv.all_conv ct
    else Conv.every_conv [Conv.arg_conv sort_disj_clause,
                          sort_disj_clause_aux] ct

(* Apply cv on the body of !x y z. ... .*)
fun forall_body_conv cv ctxt ct =
    if is_obj_all (Thm.term_of ct) then
      Conv.binder_conv (fn (_, ctxt) => forall_body_conv cv ctxt) ctxt ct
    else
      cv ct

fun norm_all_disj_sorted ctxt ct =
    Conv.every_conv [norm_all_disj ctxt,
                     forall_body_conv sort_disj_clause ctxt] ct

fun abstract_eq ctxt var eq =
    let
      val (x, T) = Term.dest_Free var
      val all_const = Const (UtilBase.All_name, (T --> boolT) --> boolT)
    in
      Drule.arg_cong_rule (Thm.cterm_of ctxt all_const)
                          (Thm.abstract_rule x (Thm.cterm_of ctxt var) eq)
    end

fun replace_disj_vars ctxt (vars, disjs) =
    let
      val vars' = vars |> map Term.dest_Free
                       |> Variable.variant_frees ctxt []
                       |> map Free
      val subst = vars ~~ vars'
    in
      (vars', map (subst_atomic subst) disjs)
    end

(* Matching for all-disj propositions *)
fun disj_prop_match ctxt (id, (tyinst, inst)) (t, (var_t, ts), (var_u, cus)) =
    let
      val thy = Proof_Context.theory_of ctxt
      val us = map Thm.term_of cus
    in
      if length var_t <> length var_u orelse length ts <> length us then [] else
      let
        (* First match the types (return [] if no match). *)
        val tys_t = map fastype_of var_t
        val tys_u = map snd var_u
        val tyinst' = fold (Sign.typ_match thy) (tys_t ~~ tys_u) tyinst
        val var_t' = map (Envir.subst_term_types tyinst') var_t
        val ts' = ts |> map (Envir.subst_term_types tyinst')
        val var_ct' = map (Thm.cterm_of ctxt) var_t'
        val cus' = cus |> map (Thm.instantiate_cterm ([], var_u ~~ var_ct'))

        (* Match the type-instantiated pattern with term. *)
        val insts = Matcher.rewrite_match_subset
                        ctxt var_t' (ts', cus') (id, (tyinst', inst))

        fun process_inst ((id', instsp'), ths) =
            let
              (* Equality between normalized t and u *)
              val eq_th = ths |> mk_disj_eq
                              |> fold (abstract_eq ctxt) (rev var_t')
                              |> apply_to_lhs (norm_all_disj_sorted ctxt)
                              |> apply_to_rhs (norm_all_disj_sorted ctxt)

              (* Equality between un-normalized t and u *)
              val t' = Util.subst_term_norm instsp' t
              val norm1 = norm_all_disj_sorted ctxt (Thm.cterm_of ctxt t')
              val cu = Thm.cterm_of ctxt (mk_all_disj (var_t', map Thm.term_of cus'))
              val norm2 = norm_all_disj_sorted ctxt cu
              val eq_th' = Util.transitive_list [norm1, eq_th, meta_sym norm2]
            in
              ((id', instsp'), eq_th')
            end
      in
        map process_inst insts
      end
      handle Type.TYPE_MATCH => []
    end

fun norm_conj_de_Morgan ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso is_disj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_disj_th,
                         Conv.arg_conv norm_conj_de_Morgan] ct
      else
        Conv.all_conv ct
    end

fun norm_conj_not_imp ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso is_imp (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.not_imp_th,
                         Conv.arg_conv norm_conj_not_imp] ct
      else
        Conv.all_conv ct
    end

fun norm_nn_cancel ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th,
                         norm_nn_cancel] ct
      else
        Conv.all_conv ct
    end

fun norm_conj ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "norm_conj: wrong type"
    in
      if is_neg t andalso is_neg (dest_not t) then
        norm_nn_cancel ct
      else if is_neg t andalso is_imp (dest_not t) then
        norm_conj_not_imp ct
      else if is_neg t andalso is_disj (dest_not t) then
        norm_conj_de_Morgan ct
      else
        Conv.all_conv ct
    end

(* DISJ items. *)

val TY_DISJ = "DISJ"

(* Given a theorem in the form of a disjunction, possibly containing
   schematic variables, return the corresponding DISJ item.
 *)
fun disj_to_ritems prem_only disj_head th =
    let
      val subs = strip_disj (prop_of' th)
    in
      if length subs = 1 then
        if Util.has_vars (Thm.prop_of th) then
          let
            fun th_to_ritem th =
                Fact (TY_DISJ,
                      UtilLogic.term_of_bool prem_only :: disj :: strip_disj (prop_of' th),
                      th)
          in
            map th_to_ritem (th |> apply_to_thm' norm_conj
                                |> UtilLogic.split_conj_th)
          end
        else
          [Fact (TY_PROP, [prop_of' th], th)]
      else let
        val tname = UtilLogic.term_of_bool prem_only :: disj_head :: subs
      in
        [Fact (TY_DISJ, tname, th)]
      end
    end

fun disj_to_update prem_only disj_head (id, sc, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = sc,
                raw_items = disj_to_ritems prem_only disj_head th}

fun get_disj_head t =
    if is_disj t then disj
    else if is_imp t then get_disj_head (dest_arg t)
    else if is_neg t andalso is_neg (dest_not t) then
      get_disj_head (dest_not (dest_not t))
    else if is_neg t andalso is_conj (dest_not t) then conj
    else if is_obj_all t orelse is_ball t then
      case dest_arg t of
          Abs (x, T, body) => get_disj_head (snd (Term.dest_abs (x, T, body)))
        | _ => imp
    else if is_neg t andalso is_ex (dest_not t) then conj
    else if is_neg t andalso is_bex (dest_not t) then conj
    else imp

(* Given a theorem th, return equivalent theorem in disjunctive form,
   with possible schematic variables. Also return whether th is
   "active", that is, whether it is originally a conjunctive goal or
   disjunctive fact, as opposed to implications.
 *)
fun analyze_disj_th ctxt th =
    let
      val head = get_disj_head (prop_of' th)
      val th' = th |> apply_to_thm' (norm_all_disj ctxt)
                   |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                   |> Util.forall_elim_sch
    in
      (head, th')
    end

(* Deconstruct the tname of a DISJ item. *)
fun dest_tname_of_disj tname =
    case tname of
        _ :: disj_head :: rest => (Thm.term_of disj_head, rest)
      | _ => raise Fail "dest_tname_of_disj: too few terms in tname."

(* Determine whether the item is for matching premises only (from the
   first entry in tname.
 *)
fun is_match_prem_only {tname, ...} =
    UtilLogic.bool_of_term (Thm.term_of (hd tname))

fun is_active_head disj_head = (not (disj_head aconv imp))

fun disj_rewr_terms ts =
    if UtilLogic.bool_of_term (hd ts) then [] else drop 2 ts

fun output_disj_fn ctxt (ts, _) =
    let
      val (match_prem, disj_head, subs) = (hd ts, hd (tl ts), tl (tl ts))
      val prefix = if UtilLogic.bool_of_term match_prem then "(match_prem) " else ""
    in
      if disj_head aconv disj then
        prefix ^ ((foldr1 mk_disj subs) |> Syntax.string_of_term ctxt)
      else if disj_head aconv conj then
        prefix ^ ((foldr1 mk_conj (map get_neg subs))
                      |> get_neg |> Syntax.string_of_term ctxt)
      else if disj_head aconv imp then
        prefix ^ ((foldr1 mk_imp (subs |> split_last |> apfst (map get_neg)
                                       |> apsnd single |> (op @)))
                      |> Syntax.string_of_term ctxt)
      else
        raise Fail "output_disj_fn: unexpected disj_head."
    end

val disj_prop_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          let
            val (var_t, ts) = (strip_all_disj pat) |> replace_disj_vars ctxt
            val (_, cus) = dest_tname_of_disj tname
            val us = map Thm.term_of cus
            val var_u = fold Term.add_vars us []
          in
            length ts = length us andalso length var_t = length var_u
          end

      fun match pat item ctxt (id, instsp) =
          let
            val {tname, prop = th, ...} = item

            val (_, cus) = dest_tname_of_disj tname
            val us = map Thm.term_of cus
            val var_u = fold Term.add_vars us []
            val (var_t, ts) = (strip_all_disj pat) |> replace_disj_vars ctxt

            fun process_perm perm =
                map (pair (map Var perm))
                    (disj_prop_match ctxt (id, instsp) (pat, (var_t, ts), (perm, cus)))

            fun process_inst (var_u, ((id', instsp'), eq_th)) =
                let
                  val eq_th' = make_trueprop_eq (meta_sym eq_th)
                  val forall_th =
                      th |> fold Thm.forall_intr (rev (map (Thm.cterm_of ctxt) var_u))
                         |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                in
                  ((id', instsp'), Thm.equal_elim eq_th' forall_th)
                end
          in
            if length var_t <> length var_u orelse length ts <> length us then []
            else var_u |> Util.all_permutes |> maps process_perm
                       |> map process_inst
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Given ct in the form p_1 | ... | p_n, apply cv to each of p_i. *)
fun ac_disj_conv cv ct =
    if is_disj (Thm.term_of ct) then
      Conv.every_conv [Conv.arg1_conv cv,
                       Conv.arg_conv (ac_disj_conv cv)] ct
    else cv ct

(* Assume ct is a disjunction, associating to the right. *)
fun reduce_disj_True ct =
    if is_disj (Thm.term_of ct) then
      ((rewr_obj_eq UtilBase.disj_True1_th)
           else_conv ((Conv.arg_conv reduce_disj_True)
                          then_conv (rewr_obj_eq UtilBase.disj_True2_th))) ct
    else
      Conv.all_conv ct

(* Handles also the case where pat is in not-conj or imp form. *)
fun match_prop ctxt (id, item2) pat =
    let
      val disj_pats = strip_disj pat

      (* th is pat'(inst), where pat' is one of the disjunctive terms
         of pat.
       *)
      fun process_inst ((id, inst), th) =
          let
            (* Construct the theorem pat'(inst) == True. *)
            val to_eqT_cv = (th RS UtilBase.eq_True_th) |> rewr_obj_eq |> Conv.try_conv

            (* Rewrite pat(inst) using the above, then rewrite to True. *)
            val pat_eqT =
                pat |> Thm.cterm_of ctxt |> norm_disj
                    |> Util.subst_thm ctxt inst
                    |> apply_to_rhs (ac_disj_conv to_eqT_cv)
                    |> apply_to_rhs reduce_disj_True
                    |> to_obj_eq
            val patT = pat_eqT RS UtilBase.eq_True_inv_th
          in
            ((id, inst), patT)
          end

      val insts1 =
          (ItemIO.match_arg ctxt (PropMatch pat) item2 (id, fo_init))
              |> filter (BoxID.has_incr_id o fst o fst)

      val insts2 =
          if length disj_pats > 1 then
            map process_inst (maps (match_prop ctxt (id, item2)) disj_pats)
          else []
    in
      insts1 @ insts2
    end

(* Given theorem ~P, cancel any disjunct that is aconv to P. It is
   possible to leave one disjunct P un-cancelled.
 *)
fun disj_cancel_cv ctxt th ct =
    if is_disj (Thm.term_of ct) then
      Conv.every_conv [Conv.arg_conv (disj_cancel_cv ctxt th),
                       Conv.try_conv (rewr_obj_eq (th RS UtilBase.or_cancel1_th)),
                       Conv.try_conv (rewr_obj_eq (th RS UtilBase.or_cancel2_th))] ct
    else
      Conv.all_conv ct

(* Given theorem P and a disjuncion theorem, return new disjunction
   theorem with ~P cancelled. If all disjuncts can be cancelled,
   return False.
 *)
fun disj_cancel_prop ctxt th prop =
    let
      val th' = if is_neg (prop_of' th) then th
                else th RS UtilBase.nn_create_th
      val prop' = prop |> apply_to_thm' (disj_cancel_cv ctxt th')
      val P = th' |> prop_of' |> dest_not
    in
      if prop_of' prop' aconv P then
        [th', prop'] MRS UtilBase.contra_triv_th
      else prop'
    end

(* Reduce a disjunction p_1 | ... | t | ... | p_n by matching ~t with
   the second item. If the disjunction contains schematic variables, t
   must have either zero or the largest number of schematic variables.
 *)
fun match_update_fn ctxt item1 item2 =
    if is_match_prem_only item1 andalso
       Util.has_vars (Thm.prop_of (#prop item1)) then [] else
    let
      val {id, prop, tname, ...} = item1
      val thy = Proof_Context.theory_of ctxt
      val (disj_head, csubs) = dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0

      fun is_priority_term t =
          if is_neg t then
            exists (is_ex orf is_bex) (strip_conj (dest_not t))
          else
            exists (is_obj_all orf is_ball) (strip_disj t)

      val has_priority_term = exists is_priority_term (map get_neg subs)

      val (NO_MATCH, SLOW_MATCH, YES_MATCH) = (0, 1, 2)
      (* Test whether to perform matching on pattern. *)
      fun test_do_match t =
          let
            val nvar = count_var t
            val neg_t = get_neg t
          in
            if not (Util.is_pattern t) then NO_MATCH
            else if length subs > 1 andalso
                    Property.is_property_prem thy neg_t then NO_MATCH
            else if has_priority_term andalso
                    not (is_priority_term neg_t) then SLOW_MATCH
            else if is_mem neg_t andalso Term.is_Var (dest_arg1 neg_t) andalso
                    null (Term.add_frees (dest_arg neg_t) []) then SLOW_MATCH
            else if nvar = 0 orelse nvar = max_nvar then YES_MATCH
            else NO_MATCH
          end

      (* Match the negation of subs[i] with th2. For each match,
         instantiate in prop all schematic variables in t, so that t
         becomes ~th2. Then remove t from prop in the instantiated
         version.
       *)
      fun get_matches i =
          let
            val t = nth subs i
            val do_match = test_do_match t
            fun process_inst ((id', inst), th) =
                let
                  val prop' = prop |> Util.subst_thm_thy thy inst
                                   |> disj_cancel_prop ctxt th
                  val sc = if do_match = SLOW_MATCH then 200 else 10
                in
                  disj_to_update false disj_head (id', SOME sc, prop') ::
                  (if count_var t > 0 then []
                   else [ShadowItem {id = id', item = item1}])
                end
          in
            if do_match = NO_MATCH then []
            else t |> get_neg |> match_prop ctxt (id, item2)
                   |> maps process_inst
          end

      fun get_matches_no_var () =
          let
            fun process_inst (id', ths) =
                let
                  val prop' = prop |> fold (disj_cancel_prop ctxt) ths
                in
                  disj_to_update false disj_head (id', SOME 1, prop') ::
                  (if is_match_prem_only item1 then []
                   else [ShadowItem {id = id', item = item1}])
                end

            fun get_match_at_id id' insts =
                insts |> filter (fn ((id, _), _) =>
                                    BoxID.is_eq_ancestor ctxt id id')
                      |> map snd |> take 1

            fun get_matches_at_id all_insts id' =
                (id', maps (get_match_at_id id') all_insts)

            fun merge_matches all_insts =
                let
                  val ids = distinct (op =) (maps (map (fst o fst)) all_insts)
                in
                  map (get_matches_at_id all_insts) ids
                end

            val _ = assert (length subs >= 2)
            val ts = [hd subs, List.last subs]
          in
            ts |> map get_neg |> map (match_prop ctxt (id, item2))
               |> merge_matches
               |> maps process_inst
          end
    in
      if max_nvar = 0 then
        get_matches_no_var ()
      else
        maps get_matches (0 upto (length subs - 1))
    end

val match_update_prfstep =
    {name = "disj_match_update",
     args = [TypedUniv TY_DISJ, PropMatch (boolVar "A")],
     func = TwoStep match_update_fn}

(* For DISJ items with a single term, of form f p1 ... pn, match t
   against each of p_i.
 *)
fun match_one_sch_fn ctxt item1 item2 =
    if is_match_prem_only item1 then [] else
    let
      val {id, tname, prop = th1, ...} = item1
      val thy = Proof_Context.theory_of ctxt
      val subs = (dest_tname_of_disj tname) |> snd |> map Thm.term_of
    in
      if length subs > 1 then [] else
      let
        val t = the_single subs
        val args = Util.dest_args t
        fun count_var t = length (Term.add_vars t [])
        val nvar = count_var t

        fun get_matches i =
            if count_var (nth args i) < nvar then [] else
            let
              val arg = nth args i
              val targ = TypedMatch (TY_TERM, arg)
              val insts = (ItemIO.match_arg ctxt targ item2 (id, fo_init))
                              |> filter (BoxID.has_incr_id o fst o fst)
              fun inst_to_updt ((id', inst), _) =
                  let
                    val th1' = Util.subst_thm_thy thy inst th1
                    val prop' = prop_of' th1'
                  in
                    if is_eq_term prop' andalso
                       RewriteTable.is_equiv_t id' ctxt (dest_eq prop')
                    then [] else [Update.thm_update (id', th1')]
                  end
            in
              maps inst_to_updt insts
            end
      in
        maps get_matches (0 upto (length args - 1))
      end
    end

val match_one_sch_prfstep =
    {name = "disj_match_one_sch",
     args = [TypedUniv TY_DISJ, TypedUniv TY_TERM],
     func = TwoStep match_one_sch_fn}

fun disj_match_iff_fn ctxt {id, tname, prop, ...} =
    if not (BoxID.has_incr_id id) then [] else
    let
      val (_, csubs) = dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_eq_term (the_single subs) andalso
              fastype_of (dest_arg (the_single subs)) = boolT) then []
      else let
        val cv = (UtilLogic.to_obj_conv ctxt) then_conv (Trueprop_conv norm_disj)
        val forward = prop |> UtilLogic.equiv_forward_th |> apply_to_thm cv
        val backward = prop |> UtilLogic.equiv_backward_th |> apply_to_thm cv
      in
        [disj_to_update false imp (id, NONE, forward),
         disj_to_update false imp (id, NONE, backward)]
      end
    end

val disj_match_iff_prfstep =
    {name = "disj_match_iff",
     args = [TypedUniv TY_DISJ],
     func = OneStep disj_match_iff_fn}

(* For active case, create box checking the next case. *)
fun disj_create_case_fn _ {id, tname, ...} =
    if not (BoxID.has_incr_id id) then [] else
    if exists Util.has_vars (map Thm.term_of tname) then [] else
    let
      val (disj_head, csubs) = dest_tname_of_disj tname
    in
      if not (is_active_head disj_head) then []
      else if length csubs = 1 then []
      else let
        val subs = map Thm.term_of csubs
      in
        [AddBoxes {id = id,
                   sc = NONE, init_assum = mk_Trueprop (hd subs)}]
      end
    end

val disj_create_case_prfstep =
    {name = "disj_create_case",
     args = [TypedUniv TY_DISJ],
     func = OneStep disj_create_case_fn}

(* item1 dominates item2 if the disjunctive terms in item1 is a subset
   of that for item2.
 *)
fun disj_shadow_fn ctxt (item1 as {tname = tname1, ...})
                   (item2 as {tname = tname2, ...}) =
    let
      val id = BoxItem.merged_id ctxt [item1, item2]
      val (disj_head1, subs1) = dest_tname_of_disj tname1
      val (disj_head2, subs2) = dest_tname_of_disj tname2
    in
      if not (BoxID.has_incr_id id) then [] else
      if not (is_active_head disj_head1) andalso
         is_active_head disj_head2 then []
      else if is_match_prem_only item1 andalso
              not (is_match_prem_only item2) then []
      else if subset (op aconvc) (subs1, subs2) then
        [ShadowItem {id = id, item = item2}]
      else []
    end

val disj_shadow_prfstep =
    {name = "disj_shadow",
     args = [TypedUniv TY_DISJ, TypedUniv TY_DISJ],
     func = TwoStep disj_shadow_fn}

val add_disj_proofsteps =
    fold ItemIO.add_item_type [
      (TY_DISJ, SOME disj_rewr_terms, SOME output_disj_fn, NONE)

    ] #> fold ItemIO.add_prop_matcher [
      (TY_DISJ, disj_prop_matcher)

    ] #> fold add_prfstep [
      match_update_prfstep, match_one_sch_prfstep, disj_match_iff_prfstep,
      disj_create_case_prfstep, disj_shadow_prfstep
    ]

(* Normalizers *)

fun split_not_imp_th th =
    th |> apply_to_thm' norm_conj_not_imp
       |> UtilLogic.split_conj_th

(* Generalized form of splitting A & B. Also deal with cases ~(A | B)
   and ~(A --> B).
 *)
fun split_conj_gen_th _ th =
    th |> apply_to_thm' norm_conj
       |> UtilLogic.split_conj_th

fun eq_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else if is_eq_term (prop_of' th) then
          let
            val (lhs, rhs) = dest_eq (prop_of' th)
          in
            if fastype_of lhs = boolT then
              map Update.thm_to_ritem
                  (UtilLogic.split_conj_th (th RS UtilBase.iffD_th))
            else
              [Fact (TY_EQ, [lhs, rhs], th)]
          end
        else [ritem]

fun property_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else if Property.is_property (prop_of' th) then
          [Fact (TY_PROPERTY, [prop_of' th], th)]
        else [ritem]

fun disj_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else let
          val t = prop_of' th
        in
          if is_neg t andalso is_conj (dest_not t) orelse
             is_disj t orelse is_imp t orelse
             is_obj_all t orelse is_ball t orelse
             is_neg t andalso is_ex (dest_not t) orelse
             is_neg t andalso is_bex (dest_not t)
          then
            let
              val (disj_head, disj_th) = analyze_disj_th ctxt th
              val prem_only = Auto2_State.lookup_prem_only ctxt t
              val disj_th = if prem_only then disj_th
                            else snd (Normalizer.meta_use_vardefs disj_th)
            in
              disj_to_ritems prem_only disj_head disj_th
            end
          else [ritem]
        end

fun logic_thm_update ctxt (id, th) =
    let
      val t = prop_of' th
    in
      if is_obj_all t orelse is_ball t orelse
         is_neg t andalso is_ex (dest_not t) orelse
         is_neg t andalso is_bex (dest_not t) orelse
         is_disj t orelse is_imp t orelse
         is_neg t andalso is_conj (dest_not t)
      then
        let
          val (disj_head, disj_th) = analyze_disj_th ctxt th
          val raw_items = disj_to_ritems true disj_head disj_th
        in
          AddItems {id = id, sc = NONE, raw_items = raw_items}
        end
      else
        Update.thm_update (id, th)
    end

val add_disj_normalizers =
    Normalizer.add_th_normalizer (
      "split_conj_gen", split_conj_gen_th

    ) #> fold Normalizer.add_normalizer [
      ("eq", eq_normalizer),
      ("property", property_normalizer),
      ("disj", disj_normalizer)
    ]

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_normalizers
val TY_DISJ = Logic_ProofSteps.TY_DISJ
