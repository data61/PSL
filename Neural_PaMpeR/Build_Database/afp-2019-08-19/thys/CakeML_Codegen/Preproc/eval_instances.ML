signature EVAL_INSTANCES =
sig
  val make: string -> theory -> theory
  val make_cmd: string -> theory -> theory

  val setup: theory -> theory

  val intro_tac:
    Proof.context -> {intros: thm list} -> tactic
  val elim_tac:
    Proof.context -> {distincts: thm list, elims: thm list, injects: thm list} -> tactic
end

structure Eval_Instances: EVAL_INSTANCES =
struct

open Dict_Construction_Util

fun intro_tac ctxt {intros} =
  REPEAT (HEADGOAL (eresolve_tac ctxt @{thms eval'E})) THEN
    HEADGOAL
      (fo_rtac @{thm eval'I} ctxt CONTINUE_WITH_FW
        [Method.assm_tac ctxt,
         SOLVED' (Tactics.rewrite_tac ctxt NONE),
         SOLVED' (fo_resolve_tac intros ctxt THEN_ALL_NEW Method.assm_tac ctxt)])

fun elim_tac ctxt {elims, distincts, injects} =
  let
    fun is_vareq prop =
      case prop of
        @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ Free _ $ _) => true
      | _ => false

    val tac =
      eresolve_tac ctxt @{thms eval'E} THEN'
        eresolve_tac ctxt elims THEN_ALL_NEW
          (econtr_tac distincts ctxt ORELSE'
            Subgoal.FOCUS (fn {context = ctxt, prems, ...} =>
              let
                val that :: wf :: rewr :: term_eq :: constr_eq :: eval = prems
                val eqs =
                  Tactics.elims_injects ctxt injects constr_eq
                  |> filter (is_vareq o Thm.prop_of)
                val subst_in_rewr =
                  Drule.infer_instantiate ctxt
                    [(("P", 0), @{cterm "\<lambda>t'. rs \<turnstile> t \<longrightarrow>* t'"})] @{thm subst}
                val rewr' = subst_in_rewr OF [term_eq, rewr]
                val tac =
                  fo_rtac (that OF [wf]) ctxt THEN_ALL_NEW
                    (SOLVED' (fo_rtac rewr' ctxt) ORELSE'
                      (fo_rtac @{thm eval_trivI} ctxt THEN'
                        SELECT_GOAL (Local_Defs.unfold_tac ctxt eqs) THEN'
                          resolve_tac ctxt eval))
              in HEADGOAL tac end) ctxt)
  in HEADGOAL tac end

val ind_flags =
  {quiet_mode = true, verbose = false, alt_name = Binding.empty,
   coind = false, no_elim = false, no_ind = false, skip_mono = false}

fun make typ_name thy =
  let
    val ctxt = Proof_Context.init_global thy
    val {ctrs, T, distincts, injects, ...} = the (Ctr_Sugar.ctr_sugar_of ctxt typ_name)
    val len = length (snd (dest_Type (unvarify_typ T)))
    val tparams = map (rpair @{sort evaluate}) (Name.invent Name.context Name.aT len)

    val typ = Embed.eval_typ (Type (typ_name, map TFree tparams))

    (* FIXME use name mangling *)
    val name = "eval_" ^ Long_Name.base_name typ_name
    val ind_head = Free (name, typ)

    val rs = Free ("rs", @{typ "rule fset"})
    val t = Free ("t", @{typ term})
    val thesis = Free ("thesis", @{typ bool})

    fun mk_parts ctr =
      let
        val (ctr_name, typ) = dest_Const (sortify @{sort evaluate} (Logic.unvarify_global ctr))
        val (arg_typs, _) = strip_type typ
        val term_params =
          length arg_typs
          |> Name.invent Name.context "t0"
          |> map (Free o rpair @{typ term})
        val ctr_params = map Free (Name.invent_names Name.context "a0" arg_typs)
      in (ctr_name, typ, term_params, ctr_params) end

    val parts = map mk_parts ctrs

    fun mk_ind_rule (ctr_name, ctr_typ, term_params, ctr_params) =
      let
        val term_applied =
          HOL_Term.list_comb (@{term term.Const} $ mk_name ctr_name, term_params)
        val ctr_applied = list_comb (Const (ctr_name, ctr_typ), ctr_params)
        val concl = HOLogic.mk_Trueprop (ind_head $ rs $ term_applied $ ctr_applied)

        fun mk_prem term_param ctr_param =
          HOLogic.mk_Trueprop
            (Const (@{const_name eval}, Embed.eval_typ (fastype_of ctr_param)) $ rs $ term_param $ ctr_param)

        val prems = map2 mk_prem term_params ctr_params
      in
        fold Logic.all (term_params @ ctr_params) (prems ===> concl)
      end

    val lthy = Class.instantiation ([typ_name], tparams, @{sort evaluate}) thy

    val ind_rules = map (pair (Binding.empty, [])) (Syntax.check_terms lthy (map mk_ind_rule parts))

    val (info, (lthy', lthy)) =
      Local_Theory.open_target lthy
      |> snd
      |> Inductive.add_ind_def ind_flags [ind_head] ind_rules [] [rs] [(Binding.name name, NoSyn)]
      ||> `Local_Theory.close_target
    val phi = Proof_Context.export_morphism lthy lthy'
    val info' = Inductive.transform_result phi info

    fun inst_tac ctxt =
      Class.intro_classes_tac ctxt [] THEN
        HEADGOAL
          (Subgoal.FOCUS (fn {context = ctxt, prems, ...} =>
            DETERM (HEADGOAL (resolve_tac ctxt [#induct info' OF prems])) THEN
            PARALLEL_ALLGOALS (Tactics.wellformed_tac ctxt)) ctxt)
    val lthy'' = Class.prove_instantiation_instance inst_tac lthy'

    fun mk_intro_elim (ctr_name, ctr_typ, term_params, ctr_params) =
      let
        val term_applied =
          HOL_Term.list_comb (@{term term.Const} $ mk_name ctr_name, term_params)
        val ctr_applied = list_comb (Const (ctr_name, ctr_typ), ctr_params)

        fun mk_prem term_param ctr_param =
          (Const (@{const_name eval'}, Embed.eval_typ (fastype_of ctr_param)) $ rs $ term_param $ ctr_param)

        val prems = map HOLogic.mk_Trueprop
          ((@{term wellformed} $ t) ::
            (@{term rewrite_rt} $ rs $ t $ term_applied) ::
            map2 mk_prem term_params ctr_params)

        val concl =
          HOLogic.mk_Trueprop (Const (@{const_name eval'}, typ) $ rs $ t $ ctr_applied)

        val intro = fold Logic.all (term_params @ ctr_params) (prems ===> concl)
        val thesis = HOLogic.mk_Trueprop thesis
        val elim =
          fold Logic.all ctr_params
            (concl ==> (fold Logic.all term_params (prems ===> thesis)) ==> thesis)
      in (intro, elim) end

    fun prove_intro goal =
      Goal.prove_future lthy'' ["rs", "t"] [] goal (fn {context = ctxt, ...} =>
        intro_tac ctxt {intros = #intrs info'})
    fun prove_elim goal =
      Goal.prove_future lthy'' ["rs", "t", "thesis"] [] goal (fn {context = ctxt, ...} =>
        elim_tac ctxt {elims = #elims info', distincts = distincts, injects = injects})

    val (intros, elims) =
      map mk_intro_elim parts
      |> split_list
      |>> map prove_intro
      ||> map prove_elim
  in
    lthy''
    |> Local_Theory.note ((Binding.empty, @{attributes [eval_data_intros]}), intros) |> snd
    |> Local_Theory.note ((Binding.empty, @{attributes [eval_data_elims]}), elims) |> snd
    |> Local_Theory.exit_global
  end

fun make_cmd s thy =
  let
    val ctxt = Proof_Context.init_global thy
    val typ_name =
      Proof_Context.read_type_name {proper = true, strict = false} ctxt s
      |> dest_Type |> fst
  in
    make typ_name thy
  end

(** setup **)

val setup =
  Derive_Manager.register_derive "evaluate" "derives an embedding relation for a datatype"
    (fn typ_name => fn param =>
      if param = "" then
        make typ_name
      else
        error "unknown parameter, expected no parameter")

end