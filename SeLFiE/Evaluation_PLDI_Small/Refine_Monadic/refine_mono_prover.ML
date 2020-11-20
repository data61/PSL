
signature REFINE_MONO_PROVER = sig
  (* A generic automatic case splitter *)
  type pat_extractor = 
    term -> (term * ((Proof.context -> conv) -> Proof.context -> conv)) option

  val gen_split_cases_tac: pat_extractor -> Proof.context -> tactic'

  (* Recognizes all patterns of the form _ (case x of ...) (case x of ...) *)
  val split_cases_tac: Proof.context -> tactic'

  (* Monotonicity prover *)
  val get_mono_thms: Proof.context -> thm list
  val add_mono_thm: thm -> Context.generic -> Context.generic
  val del_mono_thm: thm -> Context.generic -> Context.generic
  val mono_tac: Proof.context -> tactic'

  (* Monotonicity solver *)
  val untriggered_mono_tac: Proof.context -> tactic'
  val declare_mono_triggers: thm list -> morphism -> Context.generic -> Context.generic

  (* Setup *)
  val decl_setup: morphism -> Context.generic -> Context.generic
  val setup: theory -> theory

end

structure Refine_Mono_Prover : REFINE_MONO_PROVER = struct
  type pat_extractor = 
    term -> (term * ((Proof.context -> conv) -> Proof.context -> conv)) option

  (* Case Splitter, taken from Krauss' partial_function. *)
  local
    (*rewrite conclusion with k-th assumtion*)
    fun rewrite_with_asm_tac ctxt k =
      Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
        Local_Defs.unfold_tac ctxt' [nth prems k]) ctxt;
    
    fun dest_case ctxt t =
      case strip_comb t of
        (Const (case_comb, _), args) =>
          (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
             NONE => NONE
           | SOME {case_thms, ...} =>
               let
                 val lhs = Thm.prop_of (hd case_thms)
                   |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
                 val arity = length (snd (strip_comb lhs));
                 val _ = length args - arity >= 0 
                   orelse raise TERM("dest_case: arity",[t]) 
                     (* funpow on negative argument loops until stack overflow *)
                 val conv = funpow (length args - arity) Conv.fun_conv
                   (Conv.rewrs_conv (map mk_meta_eq case_thms));
               in
                 SOME (nth args (arity - 1), conv)
               end)
      | _ => NONE;
  in  
    (*split on case expressions*)
    fun gen_split_cases_tac (extract_pat:pat_extractor) 
    = Subgoal.FOCUS (fn {context=ctxt, ...} => 
      SUBGOAL (fn (t, i) => case extract_pat t of
        SOME (body, mk_conv) =>
          (case dest_case ctxt body of
             NONE => no_tac
           | SOME (arg, conv) =>
               let open Conv in
                  if Term.is_open arg then no_tac
                  else (
                      (DETERM o Induct.cases_tac ctxt false [[SOME arg]] NONE [])
                      THEN_ALL_NEW (rewrite_with_asm_tac ctxt 0)
                      THEN_ALL_NEW eresolve_tac ctxt @{thms thin_rl}
                      THEN_ALL_NEW (
                        CONVERSION (params_conv ~1 (mk_conv (K conv)) ctxt))
                    ) i
               end)
      | _ => no_tac) 1);
  end
       
  local 
    open Conv    
    fun extract @{mpat "Trueprop (_ ?t1.0 ?t2.0)"} 
        = (let 
            val last = #2 o split_last
            val (hd1,args1) = strip_comb t1
            val (hd2,args2) = strip_comb t2  
            val x1 = last args1
            val x2 = last args2
            fun mk_conv conv ctxt = 
              arg_conv (binop_conv (conv ctxt))
          in 
            if hd1 aconv hd2 andalso x1 aconv x2 then 
              SOME (t1, mk_conv)
            else NONE
          end 
          handle List.Empty => NONE)
      | extract _ = NONE
  in
    val split_cases_tac = gen_split_cases_tac extract
  end

(*
        = SOME (t,fn conv => fn ctxt => 
            arg_conv (arg_conv (abs_conv (#2 #> conv) ctxt)))
*)

  fun split_meta_conjunction thm = 
    case Thm.prop_of thm of
      @{const "Pure.conjunction"}$_$_ => let 
        val (t1,t2) = Conjunction.elim thm
      in split_meta_conjunction t1 @ split_meta_conjunction t2 end
      | _ => [thm]

  structure Mono_Thms = Named_Sorted_Thms (
    val name = @{binding refine_mono} 
    val description = "Refinement Framework: Monotonicity theorems"
    val sort = K I
    val transform = fn context => split_meta_conjunction #> map (norm_hhf (Context.proof_of context))
  )

  val get_mono_thms = Mono_Thms.get
  val add_mono_thm = Mono_Thms.add_thm
  val del_mono_thm = Mono_Thms.del_thm

  fun mono_tac ctxt = REPEAT_ALL_NEW (
    FIRST' [
      Method.assm_tac ctxt,
      resolve_tac ctxt (Mono_Thms.get ctxt),
      split_cases_tac ctxt
    ]
  )

  fun untriggered_mono_tac ctxt = mono_tac ctxt 
    THEN_ALL_NEW (TRY o Tagged_Solver.solve_tac ctxt)

  val mono_solver_bnd = @{binding refine_mono}
  val mono_solver_name = "Refine_Mono_Prover.refine_mono" (* TODO: HACK! *)

  val declare_mono_triggers =
    Tagged_Solver.add_triggers mono_solver_name

  val decl_setup = 
    Tagged_Solver.declare_solver 
      @{thms monoI monotoneI[of "(\<le>)" "(\<le>)"]} mono_solver_bnd
      "Refine_Monadic: Monotonicity prover" 
      mono_tac

  val setup = I
    #> Mono_Thms.setup
end


