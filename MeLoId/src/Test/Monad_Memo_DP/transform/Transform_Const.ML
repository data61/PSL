structure Transform_Const = struct
  val pureappN = @{const_name Pure_Monad.App}
  fun pureapp tm = Const (pureappN, dummyT) $ tm

  type MONAD_CONSTS = {
    monad_name: string,
    mk_stateT: typ -> typ,
    return: term -> term,
    app: (term * term) -> term,
    if_termN: string,
    checkmemVN: string,
    rewrite_app_beta_conv: conv
  }
  
  val state_monad: MONAD_CONSTS =
    let
      val memT = TFree ("MemoryType", @{sort type})
      val memT = dummyT
    
      fun mk_stateT tp =
        Type (@{type_name State_Monad.state}, [memT, tp])
    
      val returnN = @{const_name State_Monad.return}
      fun return tm = Const (returnN, dummyT --> mk_stateT dummyT) $ tm
    
      val appN = @{const_name State_Monad_Ext.fun_app_lifted}
      fun app (tm0, tm1) = Const (appN, dummyT) $ tm0 $ tm1
    
      fun checkmem'C ctxt = Transform_Misc.get_const_pat ctxt "checkmem'"
      fun checkmem' ctxt param body = checkmem'C ctxt $ param $ body
    
      val checkmemVN = "checkmem"
      val checkmemC = @{const_name "state_mem_defs.checkmem"}

      fun rewrite_app_beta_conv ctm =
        case Thm.term_of ctm of
          Const (@{const_name State_Monad_Ext.fun_app_lifted}, _)
            $ (Const (@{const_name State_Monad.return}, _) $ Abs _)
            $ (Const (@{const_name State_Monad.return}, _) $ _)
            => Conv.rewr_conv @{thm State_Monad_Ext.return_app_return_meta} ctm
        | _ => Conv.no_conv ctm

    in {
      monad_name = "state",
      mk_stateT = mk_stateT,
      return = return,
      app = app,
      if_termN = @{const_name State_Monad_Ext.if\<^sub>T},
      checkmemVN = checkmemVN,
      rewrite_app_beta_conv = rewrite_app_beta_conv
    } end

  val heap_monad: MONAD_CONSTS =
    let
      fun mk_stateT tp =
        Type (@{type_name Heap_Monad.Heap}, [tp])
    
      val returnN = @{const_name Heap_Monad.return}
      fun return tm = Const (returnN, dummyT --> mk_stateT dummyT) $ tm
    
      val appN = @{const_name Heap_Monad_Ext.fun_app_lifted}
      fun app (tm0, tm1) = Const (appN, dummyT) $ tm0 $ tm1
    
      fun checkmem'C ctxt = Transform_Misc.get_const_pat ctxt "checkmem'"
      fun checkmem' ctxt param body = checkmem'C ctxt $ param $ body
    
      val checkmemVN = "checkmem"
      val checkmemC = @{const_name "heap_mem_defs.checkmem"}

      fun rewrite_app_beta_conv ctm =
        case Thm.term_of ctm of
          Const (@{const_name Heap_Monad_Ext.fun_app_lifted}, _)
            $ (Const (@{const_name Heap_Monad.return}, _) $ Abs _)
            $ (Const (@{const_name Heap_Monad.return}, _) $ _)
            => Conv.rewr_conv @{thm Heap_Monad_Ext.return_app_return_meta} ctm
        | _ => Conv.no_conv ctm
    in {
      monad_name = "heap",
      mk_stateT = mk_stateT,
      return = return,
      app = app,
      if_termN = @{const_name Heap_Monad_Ext.if\<^sub>T},
      checkmemVN = checkmemVN,
      rewrite_app_beta_conv = rewrite_app_beta_conv
    } end

  val monad_consts_dict = [
    ("state", state_monad),
    ("heap", heap_monad)
  ]

  fun get_monad_const name =
    case AList.lookup op= monad_consts_dict name of
      SOME consts => consts
    | NONE => error("unrecognized monad: " ^ name ^ " , choices: " ^ commas (map fst monad_consts_dict));

end

