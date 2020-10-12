signature PO_NORMALIZER = sig 
  type norm_set = {
    trans_rules : thm list, (* Transitivity rules, of form "R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" *)
    cong_rules : thm list, (* Congruence rules, of form: "\<lbrakk> R1 a1 b1; ... \<rbrakk> \<Longrightarrow> R (f a1 ...) (f b1 ...)" *)
    norm_rules : thm list, (* Normalization rules, of form: "R f g" *)
    refl_rules : thm list (* Reflexivity rules, of form: "R x x"*)
  }

  val gen_norm_tac : norm_set -> Proof.context -> tactic'
  val gen_norm_rule : thm list -> norm_set -> Proof.context -> thm -> thm
end

structure PO_Normalizer : PO_NORMALIZER = struct
  type norm_set = {
    trans_rules : thm list, (* Transitivity rules, of form "R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" *)
    cong_rules : thm list, (* Congruence rules, of form: "\<lbrakk> R1 a1 b1; ... \<rbrakk> \<Longrightarrow> R (f a1 ...) (f b1 ...)" *)
    norm_rules : thm list, (* Normalization rules, of form: "R f g" *)
    refl_rules : thm list (* Reflexivity rules, of form: "R x x"*)
  }

  val cfg_trace = 
    Attrib.setup_config_bool @{binding "norm_rel_trace"} (K false)

  val cfg_depth_limit = 
    Attrib.setup_config_int @{binding "norm_rel_depth_limit"} (K ~1)


  fun gen_norm_tac {trans_rules, cong_rules, norm_rules, refl_rules} ctxt = let
    val do_trace = Config.get ctxt cfg_trace

    fun trace_tac str _ st = if do_trace then 
      (tracing str; Seq.single st)
    else Seq.single st
    val print_tac = if do_trace then print_tac else (K (K all_tac))

    val depth_limit = Config.get ctxt cfg_depth_limit

    fun norm_tac d ctxt i st = let
      val transr_tac = resolve_tac ctxt trans_rules
      val congr_tac = resolve_tac ctxt cong_rules
      val rewrr_tac = resolve_tac ctxt norm_rules
      val solver_tac = resolve_tac ctxt refl_rules

      val cong_tac = (transr_tac THEN' (
        (congr_tac THEN' trace_tac "cong") THEN_ALL_NEW_FWD norm_tac (d+1) ctxt))
      val rewr_tac = (transr_tac THEN' (SOLVED' rewrr_tac) 
        THEN' trace_tac "rewr" THEN' transr_tac THEN' norm_tac (d+1) ctxt)
      val solve_tac = SOLVED' solver_tac THEN' (K (print_tac ctxt "solved"))
    in 
      if depth_limit>=0 andalso d>depth_limit then
        (K (print_tac ctxt "Norm-Depth limit reached"))
        THEN' solve_tac
      else
        (K (print_tac ctxt ("Normalizing ("^ string_of_int d  ^")"))) THEN'
        (TRY o cong_tac)
        THEN' (TRY o rewr_tac)
        THEN' solve_tac
    end i st
  in norm_tac 1 ctxt end

  fun gen_norm_rule init_thms norm_set ctxt thm = let
    val orig_ctxt = ctxt
    val ((_,[thm]),ctxt) = Variable.import false [thm] ctxt

    fun tac ctxt = 
      eresolve_tac ctxt init_thms
      THEN' gen_norm_tac norm_set ctxt

    val concl = Thm.concl_of thm
    val x = Var (("x",0),@{typ prop})
    val t = @{mk_term "PROP ?concl \<Longrightarrow> PROP ?x"}

    val thm2 = Goal.prove ctxt [] [] t 
      (fn {context = ctxt, ...} => tac ctxt 1)
    
    val thm = thm RS thm2 
    val [thm] = Variable.export ctxt orig_ctxt [thm]
  in
    thm
  end
  
end
