structure Transform_Misc = struct
  fun import_function_info term_opt ctxt =
    case term_opt of
      SOME tm => (case Function_Common.import_function_data tm ctxt of
        SOME info => info
      | NONE => raise TERM("not a function", [tm]))
    | NONE => (case Function_Common.import_last_function ctxt of
        SOME info => info
      | NONE => error "no function defined yet")

  fun get_const_pat ctxt tm_pat =
    let val (Const (name, _)) = Proof_Context.read_const {proper=false, strict=false} ctxt tm_pat
    in Const (name, dummyT) end

  fun head_of (func_info: Function.info) = #fs func_info |> the_single
  fun bind_of (func_info: Function.info) = #fnames func_info |> the_single

  fun totality_of (func_info: Function.info) =
    func_info |> #totality |> the;

  fun rel_of (func_info: Function.info) ctxt =
    Inductive.the_inductive ctxt (#R func_info) |> snd |> #eqs |> the_single;

  fun the_element l =
    if tl l |> find_first (not o equal (hd l)) |> is_none
      then hd l
      else (@{print} l; error "inconsistent n_args")

  fun add_function bind defs =
    let
      val fixes = [(bind, NONE, NoSyn)];
      val specs = map (fn def => (((Binding.empty, []), def), [], [])) defs
      val pat_completeness_auto = fn ctxt =>
        Pat_Completeness.pat_completeness_tac ctxt 1
        THEN auto_tac ctxt
    in
      Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto
    end

  fun behead head tm =
    let
      val head_nargs = strip_comb head |> snd |> length
      val (tm_head, tm_args) = strip_comb tm
      val (tm_args0, tm_args1) = chop head_nargs tm_args
      val tm_head' = list_comb (tm_head, tm_args0)
      val _ = if Term.aconv_untyped (head, tm_head')
        then () else raise TERM("head does not match", [head, tm_head'])
    in
      (tm_head', tm_args1)
    end

  fun term_name tm =
    if is_Free tm orelse is_Const tm
      then Term.term_name tm
      else raise TERM("not an atom, explicit name required", [tm])

  fun locale_term lthy locale_name term_name =
    Syntax.read_term lthy (Long_Name.qualify locale_name term_name)

  fun locale_thms lthy locale_name thms_name =
    Proof_Context.get_thms lthy (Long_Name.qualify locale_name thms_name)

  fun uncurry tm =
    let
      val arg_typs = fastype_of tm |> binder_types
      val arg_names = Name.invent_list [] "a" (length arg_typs)
      val args = map Free (arg_names ~~ arg_typs)
      val args_tuple = HOLogic.mk_tuple args
      val tm' = list_comb (tm, args) |> HOLogic.tupled_lambda args_tuple
    in
      tm'
    end
end
