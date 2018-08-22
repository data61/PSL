fun list_conv (head_conv, arg_convs) lthy =
  Library.foldl (uncurry Conv.combination_conv) (head_conv lthy, map (fn conv => conv lthy) arg_convs)

fun eta_conv1 ctxt =
  (Conv.abs_conv (K Conv.all_conv) ctxt)
  else_conv
  (Thm.eta_long_conversion then_conv Conv.abs_conv (K Thm.eta_conversion) ctxt)

fun eta_conv_n n =
  funpow n (fn conv => fn ctxt => eta_conv1 ctxt then_conv Conv.abs_conv (fn (_, ctxt) => conv ctxt) ctxt) (K Conv.all_conv)

fun conv_changed conv ctm =
  let val eq = conv ctm
  in if Thm.is_reflexive eq then Conv.no_conv ctm else eq end

fun repeat_sweep_conv conv =
  Conv.repeat_conv o conv_changed o Conv.top_sweep_conv conv

val app_mark_conv = Conv.rewr_conv @{thm App_def[symmetric]}
val app_unmark_conv = Conv.rewr_conv @{thm App_def}
val wrap_mark_conv = Conv.rewr_conv @{thm Wrap_def[symmetric]}

structure Transform_Term = struct

fun eta_expand tm =
  let
    val n_args = Integer.min 1 (length (binder_types (fastype_of tm)))
    val (args, body) = Term.strip_abs_eta n_args tm
  in
    Library.foldr (uncurry Term.absfree) (args, body)
  end

fun is_ctr_sugar ctxt tp_name =
  is_some (Ctr_Sugar.ctr_sugar_of ctxt tp_name)

fun type_nargs tp = tp |> strip_type |> fst |> length
fun term_nargs tm = type_nargs (fastype_of tm)

fun
  lift_type (monad_consts: Transform_Const.MONAD_CONSTS) ctxt tp = #mk_stateT monad_consts  (lift_type' monad_consts ctxt tp)
and
  lift_type' monad_consts ctxt (tp as Type (@{type_name fun}, _))
    = lift_type' monad_consts ctxt (domain_type tp) --> lift_type monad_consts ctxt (range_type tp)
| lift_type' monad_consts ctxt (tp as Type (tp_name, tp_args))
    = if is_ctr_sugar ctxt tp_name then Type (tp_name, map (lift_type' monad_consts ctxt) tp_args)
      else if null tp_args then tp (* int, nat, \<dots> *)
      else raise TYPE("not a ctr_sugar", [tp], [])
| lift_type' _ _ tp = tp

fun is_atom_type monad_consts ctxt tp =
  tp = lift_type' monad_consts ctxt tp

fun is_1st_type monad_consts ctxt tp =
  body_type tp :: binder_types tp
  |> forall (is_atom_type monad_consts ctxt)

fun orig_atom ctxt atom_name =
  Proof_Context.read_term_pattern ctxt atom_name

fun is_1st_term monad_consts ctxt tm =
  is_1st_type monad_consts ctxt (fastype_of tm)

fun is_1st_atom monad_consts ctxt atom_name =
  is_1st_term monad_consts ctxt (orig_atom ctxt atom_name)

fun wrap_1st_term monad_consts ctxt tm n_args_opt inner_wrap =
  let
    val n_args = the_default (term_nargs tm) n_args_opt
    val (vars_name_typ, body) = Term.strip_abs_eta n_args tm
    fun wrap (name_typ, (conv, tm)) = (
      eta_conv1 ctxt then_conv Conv.abs_conv (K conv) ctxt then_conv wrap_mark_conv,
      #return monad_consts (Term.absfree name_typ tm)
    )
    val (conv, result) = Library.foldr wrap (vars_name_typ, (
      if inner_wrap then (wrap_mark_conv, #return monad_consts body) else (Conv.all_conv, body) 
    ))
    
  in
    (K conv, result)
  end

fun lift_1st_atom monad_consts ctxt atom (name, tp) =
  let
    val (arg_typs, body_typ) = strip_type tp

    val n_args = term_nargs (orig_atom ctxt name)

    val (arg_typs, body_arg_typs) = chop n_args arg_typs
    val arg_typs' = map (lift_type' monad_consts ctxt) arg_typs
    val body_typ' = lift_type' monad_consts ctxt (body_arg_typs ---> body_typ)

    val tm' = atom (name, arg_typs' ---> body_typ') (* " *)
  in
    wrap_1st_term monad_consts ctxt tm' (SOME n_args) true
  end

fun fixed_args head_n_args tm =
  let
    val (tm_head, tm_args) = strip_comb tm
    val n_tm_args = length tm_args
  in
    head_n_args tm_head
    |> Option.mapPartial (fn n_args =>
      if n_tm_args > n_args then NONE
      else if n_tm_args < n_args then raise TERM("need " ^ string_of_int n_args ^ " args", [tm])
      else SOME (tm_head, tm_args))
  end

fun lift_abs' monad_consts ctxt (name, typ) cont lift_dict body =
  let
    val free = Free (name, typ)
    val typ' = lift_type' monad_consts ctxt typ
    val freeT' = Free (name, typ')
    val freeT = #return monad_consts (freeT')

    val lift_dict' = if is_atom_type monad_consts ctxt typ
      then lift_dict
      else (free, (K wrap_mark_conv, freeT))::lift_dict
    val (conv_free, body_free) = (cont (lift_dict') body)

    val body' = lambda freeT' body_free
    fun conv lthy =
      eta_conv1 ctxt then_conv Conv.abs_conv (fn (_, lthy') => conv_free lthy') lthy
  in
    (conv, body')
  end

fun lift_arg monad_consts ctxt lift_dict tm =
  (*
  let
    val (conv, tm') = lift_term ctxt lift_dict (eta_expand tm)
    fun conv' ctxt = Conv.try_conv (eta_conv1 ctxt) then_conv (conv ctxt)
  in
    (conv', tm')
  end

  eta_expand AFTER lifting
  *)
  lift_term monad_consts ctxt lift_dict tm
and lift_term monad_consts ctxt lift_dict tm = let
  val case_terms = Ctr_Sugar.ctr_sugars_of ctxt |> map #casex

  fun lookup_case_term tm =
    find_first (fn x => Term.aconv_untyped (x, tm)) case_terms

  val check_cont = lift_term monad_consts ctxt
  val check_cont_arg = lift_arg monad_consts ctxt

  fun check_const tm =
    case tm of
      Const (_, typ) => (
        case Transform_Data.get_dp_info (#monad_name monad_consts) ctxt tm of
          SOME {new_headT=Const (name, _), ...} => SOME (K Conv.all_conv, Const (name, lift_type monad_consts ctxt typ))
        | SOME {new_headT=tm', ...} => raise TERM("not a constant", [tm'])
        | NONE => NONE)
    | _ => NONE

  fun check_1st_atom tm =
    case tm of
      Const (name, typ) =>
        if is_1st_atom monad_consts ctxt name then SOME (lift_1st_atom monad_consts ctxt Const (name, typ)) else NONE
    | Free (name, typ) =>
        if is_1st_atom monad_consts ctxt name then SOME (lift_1st_atom monad_consts ctxt Free (name, typ)) else NONE
    | _ => (*
        if is_1st_term ctxt tm andalso exists_subterm (AList.defined (op aconv) lift_dict) tm
          then SOME (wrap_1st_term tm NONE)
          else *) NONE

(*
  fun check_dict tm =
    (* TODO: map -> mapT, dummyT *)
    AList.lookup Term.aconv_untyped lift_dict tm
    |> Option.map (fn tm' =>
      if is_Const tm
        then (@{assert} (is_Const tm'); map_types (K (lift_type ctxt (type_of tm))) tm')
        else tm')
*)

  fun check_dict tm =
    AList.lookup Term.aconv_untyped lift_dict tm

  fun check_if tm =
    fixed_args (fn head => if Term.aconv_untyped (head, @{term If}) then SOME 3 else NONE) tm
    |> Option.map (fn (_, args) =>
      let
        val (arg_convs, args') = map (check_cont lift_dict) args |> split_list
        val conv = list_conv (K Conv.all_conv, arg_convs)
        val tm' = list_comb (Const (#if_termN monad_consts, dummyT), args')
      in
        (conv, tm')
      end)

  fun check_abs tm =
    case tm of
      Abs (name, typ, body) =>
        let
          val (name', body') = Term.dest_abs (name, typ, body)
          val (conv, tm') = lift_abs' monad_consts ctxt (name', typ) check_cont lift_dict body'
          fun convT lthy = conv lthy then_conv wrap_mark_conv
          val tmT = #return monad_consts tm'
        in SOME (convT, tmT) end
    | _ => NONE

  fun check_case tm =
    fixed_args (lookup_case_term #> Option.map (fn cs => term_nargs cs - 1)) tm
    |> Option.map (fn (head, args) =>
      let
        val (case_name, case_type) = lookup_case_term head |> the |> dest_Const
        val ((clause_typs, _), _) =
          strip_type case_type |>> split_last
        
        val clase_nparams = clause_typs |> map type_nargs
        (* ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) |> type_nargs = 1*)
  
        fun lift_clause n_param clause =
          let
            val (vars_name_typ, body) = Term.strip_abs_eta n_param clause
            val abs_lift_wraps = map (lift_abs' monad_consts ctxt) vars_name_typ
            val lift_wrap = Library.foldr (op o) (abs_lift_wraps, I) check_cont
            val (conv, clauseT) = lift_wrap lift_dict body
          in
            (conv, clauseT)
          end
  
        val head' = Const (case_name, dummyT) (* clauses are sufficient for type inference *)
        val (convs, clauses') = map2 lift_clause clase_nparams args |> split_list

        fun conv lthy = list_conv (K Conv.all_conv, convs) lthy then_conv wrap_mark_conv
        val tm' = #return monad_consts (list_comb (head', clauses'))
      in
        (conv, tm')
      end)

  fun check_app tm =
    case tm of
      f $ x =>
        let
          val (f_conv, tmf) = check_cont lift_dict f
          val (x_conv, tmx) = check_cont_arg lift_dict x
          val tm' = #app monad_consts (tmf, tmx)
          fun conv lthy = Conv.combination_conv (f_conv lthy then_conv app_mark_conv) (x_conv lthy)
        in
          SOME (conv, tm')
        end
    | _ => NONE

  fun check_pure tm =
    if tm |> exists_subterm (AList.defined (op aconv) lift_dict)
      orelse not (is_1st_term monad_consts ctxt tm)
      then NONE
      else SOME (wrap_1st_term monad_consts ctxt tm NONE true)

  fun choke tm =
    raise TERM("cannot process term", [tm])

  val checks = [
    check_pure,
    check_const,
    check_case,
    check_if,
    check_abs,
    check_app,
    check_dict,
    check_1st_atom,
    choke
  ]
  in get_first (fn check => check tm) checks |> the end

fun rewrite_pureapp_beta_conv ctm =
  case Thm.term_of ctm of
    Const (@{const_name Pure_Monad.App}, _)
      $ (Const (@{const_name Pure_Monad.Wrap}, _) $ Abs _)
      $ (Const (@{const_name Pure_Monad.Wrap}, _) $ _)
      => Conv.rewr_conv @{thm Wrap_App_Wrap} ctm
  | _ => Conv.no_conv ctm

fun monadify monad_consts ctxt tm =
  let
    val (_, tm) = lift_term monad_consts ctxt [] tm
    (*val tm = rewrite_return_app_return tm*)
    val tm = Syntax.check_term ctxt tm
  in
    tm
  end

fun wrap_head (monad_consts: Transform_Const.MONAD_CONSTS) head n_args =
  Library.foldr
    (fn (typ, tm) => #return monad_consts (absdummy typ tm))
    (replicate n_args dummyT, list_comb (head, rev (map_range Bound n_args)))

fun lift_head monad_consts ctxt head n_args =
  let
    val dest_head = if is_Const head then dest_Const else dest_Free
    val (head_name, head_typ) = dest_head head
    val (arg_typs, body_typ) = strip_type head_typ
    val (arg_typs0, arg_typs1) = chop n_args arg_typs
    val arg_typs0' = map (lift_type' monad_consts ctxt) arg_typs0
    val arg_typs1T = lift_type monad_consts ctxt (arg_typs1 ---> body_typ)
    val head_typ' = arg_typs0' ---> arg_typs1T
    val head' = Free (head_name, head_typ')

    val (head_conv, headT) = wrap_1st_term monad_consts ctxt head' (SOME n_args) false
  in
    (head', (head_conv, headT))
  end

fun lift_equation monad_consts ctxt (lhs, rhs) memoizer_opt =
  let
    val (head, args) = strip_comb lhs
    val n_args = length args
    val (head', (head_conv, headT)) = lift_head monad_consts ctxt head n_args
    val args' = args |> map (map_aterms (fn tm => tm |> map_types
      (if is_Const tm then K dummyT else lift_type' monad_consts ctxt)))
    val lhs' = list_comb (head', args')

    val frees = fold Term.add_frees args []
     |> filter_out (is_atom_type monad_consts ctxt o snd)
    
    val lift_dict_args = frees |> map (fn (name, typ) => (
      Free (name, typ), 
      (K wrap_mark_conv,
       #return monad_consts (Free (name, lift_type' monad_consts ctxt typ)))
    ))
    val lift_dict = (head, (head_conv, headT)) :: lift_dict_args
    val (rhs_conv, rhsT) = lift_term monad_consts ctxt lift_dict rhs

    val rhsT_memoized = case memoizer_opt of
      SOME memoizer =>
        memoizer
        $ HOLogic.mk_tuple args
        $ rhsT
    | NONE => rhsT

    val eqs' = (lhs', rhsT_memoized) |> HOLogic.mk_eq |> HOLogic.mk_Trueprop
  in
    (rhs_conv, eqs', n_args)
  end


end
