signature EMBED =
sig
  val eval_typ: typ -> typ

  datatype embed_proof = No_Auto | Simp | Eval
  datatype cert_proof = Cert | Skip

  type embed_opts = {proof: embed_proof, cert: cert_proof}
  val default_opts: embed_opts

  val embed_def: (binding * Attrib.binding) -> term list -> embed_opts -> local_theory ->
    ((term * thm * term * thm option) * local_theory)
  val embed_def_cmd: Attrib.binding -> binding -> string list -> embed_opts -> local_theory ->
    Proof.state

  type fun_info =
    {rs: term,
     rs_def: thm,
     base_embeds: thm list,
     consts: (string * int) list,
     inducts: thm list option,
     simps: thm list}

  val embed_tac: fun_info -> cert_proof -> Proof.context -> int -> tactic
  val embed_ext_tac: fun_info -> cert_proof -> Proof.context -> int -> tactic

  val debug: bool Config.T
end

structure Embed: EMBED =
struct

(* FIXME copied from skip_proof.ML *)

val (_, make_thm_cterm) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (@{binding eval_oracle}, I)))

fun make_thm ctxt prop = make_thm_cterm (Thm.cterm_of ctxt prop)

fun cheat_tac ctxt i st =
  resolve_tac ctxt [make_thm ctxt (Var (("A", 0), propT))] i st

(** utilities **)
(* FIXME copied from dict_construction.ML *)

val debug = Attrib.setup_config_bool @{binding "embed_debug"} (K false)

fun if_debug ctxt f =
  if Config.get ctxt debug then f () else ()

fun ALLGOALS' ctxt = if Config.get ctxt debug then ALLGOALS else PARALLEL_ALLGOALS
fun prove' ctxt = if Config.get ctxt debug then Goal.prove ctxt else Goal.prove_future ctxt
fun prove_common' ctxt = Goal.prove_common ctxt (if Config.get ctxt debug then NONE else SOME ~1)


fun eval_typ typ = @{typ "rule fset"} --> @{typ term} --> typ --> @{typ bool}

datatype embed_proof = No_Auto | Simp | Eval
datatype cert_proof = Cert | Skip

type embed_opts = {proof: embed_proof, cert: cert_proof}

val default_opts = {proof = Simp, cert = Cert}

open Dict_Construction_Util

fun all_typs (Type (typ, args)) = typ :: maps all_typs args
  | all_typs _ = []

val code_tac =
  Code_Simp.static_tac
    {consts = [@{const_name rules'}, @{const_name fmdom}, @{const_name fmempty}, @{const_name fmupd}],
     ctxt = @{context},
     simpset = NONE}

type fun_info =
  {rs: term,
   rs_def: thm,
   base_embeds: thm list,
   consts: (string * int) list,
   inducts: thm list option,
   simps: thm list}

fun embed_ext_tac {inducts, simps, rs_def, base_embeds, consts, ...} cert =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, concl, ...} =>
    let
      val _ = if_debug ctxt (fn () =>
        tracing ("Proving " ^ Syntax.string_of_term ctxt (Thm.term_of concl)));

      val elims = Named_Theorems.get ctxt @{named_theorems eval_data_elims}
      val names = map fst consts

      fun get_vars t =
        case t of
          Const (@{const_name eval'}, _) $ _ $ t $ x =>
            (map Free (Term.add_frees t []), rev (map Free (Term.add_frees x [])))

      val (tss, xss) =
        Logic.dest_conjunctions (Thm.term_of concl)
        |> map (HOLogic.dest_Trueprop o Logic.strip_imp_concl)
        |> map get_vars
        |> split_list

      val conv =
        Refine_Util.HOL_concl_conv (K (Conv.arg_conv (Conv.rewrs_conv (map safe_mk_meta_eq simps)))) ctxt

      val cert_tac =
        case cert of
          Skip => cheat_tac ctxt
        | Cert => SOLVED' (Tactics.eval_tac ctxt base_embeds)
    in
      maybe_induct_tac inducts xss tss ctxt THEN ALLGOALS' ctxt
        (CONVERSION conv THEN'
          TRY' (REPEAT_ALL_NEW (eresolve_tac ctxt elims)) THEN'
          resolve_tac ctxt @{thms eval_compose} CONTINUE_WITH_FW
            [Tactics.wellformed_tac ctxt,
             (* requires full rewriting: rule from ruleset may apply only if arguments are
                rewritten first *)
             Tactics.rewrite1_tac ctxt (SOME {rs_def = rs_def, simps = simps, restrict = SOME names}),
             cert_tac])
    end)

fun embed_tac info cert ctxt =
  let
    val {consts, ...} = info
    fun loop 0 = K all_tac
      | loop n =
          fo_rtac @{thm eval'_ext} ctxt CONTINUE_WITH_FW
            [Tactics.wellformed_tac ctxt,
             loop (n - 1)]
    val loops = map (loop o snd) consts
  in
    SELECT_GOAL
      (HEADGOAL (Goal.conjunction_tac CONTINUE_WITH loops) THEN
        Goal.recover_conjunction_tac) CONTINUE_WITH
      [TRY' (norm_all_conjunction_tac ctxt) THEN' embed_ext_tac info cert ctxt]
  end

fun extend ctxt thm =
  let
    val (lhs, _) = Logic.dest_equals (Thm.prop_of thm)
    val (head, args) = Term.strip_comb lhs

    val pretty = Syntax.string_of_term ctxt (Thm.prop_of thm)

    val fun_type = can (Term.dest_funT o fastype_of) head
  in
    if not fun_type then
      error ("Implementation restriction: can't deal with non-function constant: " ^ pretty)
    else if null args then
      @{thm embed_ext} OF [thm]
    else
      thm
  end

fun embed_def (binding, def_binding) terms {proof, cert} lthy =
  let
    val (consts, _) = Syntax.check_terms lthy terms |> map dest_Const |> split_list
    val _ =
      Pretty.block
        (Pretty.str "Defining the embedding(s) of " ::
          Pretty.separate "" (map (pretty_const lthy) consts))
      |> Pretty.writeln

    val config_ctxt =
      lthy
      |> Config.put Constructor_Funs.enabled true
      |> Config.put Pattern_Compatibility.enabled true
      |> Config.put Dynamic_Unfold.enabled true

    val code_eqss = Dict_Construction.group_code_eqs config_ctxt consts

    val raw_eqs =
      flat code_eqss
      |> maps (snd o snd)
      |> map snd
      |> cat_options
      |> map (Thm.prop_of o extend lthy o Conv.fconv_rule (Dict_Construction.normalizer_conv lthy))

    val eqs = map HOL_Term.mk_eq raw_eqs
    val rs = mk_fset @{typ "term \<times> term"} eqs

    val C_info =
      maps all_consts raw_eqs
      |> map snd
      |> maps all_typs
      |> distinct op =
      |> map (fn typ => Option.map (pair typ) (try (HOL_Datatype.mk_dt_def lthy) typ))
      |> cat_options
      |> map (apfst mk_name)
      |> mk_fmap (@{typ name}, @{typ dt_def})

    val C_info_binding = Binding.qualify_name true binding "C_info"

    val ((rs_term, (_, rs_def)), lthy') =
      Local_Theory.define ((binding, NoSyn), (def_binding, rs)) lthy
    val ((C_info_term, (_, C_info_def)), lthy') =
      Local_Theory.define ((C_info_binding, NoSyn), ((Thm.def_binding C_info_binding, []), C_info)) lthy'
    val prop = HOLogic.mk_Trueprop (@{term rules} $ C_info_term $ rs_term)

    fun tac eval ctxt =
      HEADGOAL (fo_rtac @{thm rules_approx} ctxt) THEN
        Local_Defs.unfold_tac ctxt [rs_def, C_info_def] THEN
        (if eval then
           HEADGOAL (eval_tac ctxt)
         else
           Local_Defs.unfold_tac ctxt @{thms rules'_def} THEN
             HEADGOAL (REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI})) THEN
             ALLGOALS' ctxt (code_tac ctxt))

    val thm =
      case proof of
        No_Auto => NONE
      | Eval => SOME (prove' lthy' [] [] prop (fn {context = ctxt, ...} => tac true ctxt))
      | Simp => SOME (prove' lthy' [] [] prop (fn {context = ctxt, ...} => tac false ctxt))

    val _ = Option.map (on_thms_complete (fn () => writeln "Proved wellformedness") o single) thm

    fun prove_embed code_eqs (base_simps, base_embeds) =
      if exists (null o snd o snd) code_eqs then
        (* constructor *)
        (base_simps, base_embeds)
      else
        (* proper definition *)
        let
          val (consts, simps) =
            map (fn (name, (_, eqs)) =>
              let
                val (count, eqs) =
                  split_list (map (apfst (length o fst)) eqs)
                  |>> distinct op = |>> the_single
                  ||> cat_options
              in ((name, count), eqs) end) code_eqs
            |> split_list
            ||> flat ||> map (Conv.fconv_rule (Dict_Construction.normalizer_conv lthy'))

          (* FIXME the whole treatment of type variables here is probably wrong *)

          val const_terms =
            map (Const o rpair dummyT o fst) consts
            |> Syntax.check_terms lthy'

          val fun_induct = Option.mapPartial #inducts (try (Function.get_info lthy') (hd const_terms))
          val bnf_induct = induct_of_bnf_const lthy' (hd const_terms)

          val inducts = merge_options (fun_induct, bnf_induct)

          val _ =
            if is_none inducts andalso length simps > 1 then
              warning ("No induction rule found (could be problematic). Did you run this through declassify?")
            else ()

          val info: fun_info =
            {rs = rs_term,
             rs_def = rs_def,
             base_embeds = base_embeds,
             consts = consts,
             simps = simps @ base_simps,
             inducts = inducts}

          fun mk_goal (const, _) =
            Term.list_comb
              (Const (@{const_name eval'}, eval_typ dummyT),
               [rs_term, @{const Const} $ mk_name const, Const (const, dummyT)])
            |> HOLogic.mk_Trueprop

          val goals = Syntax.check_terms lthy' (map mk_goal consts)

          val embeds =
            prove_common' lthy' [] [] goals (fn {context = ctxt, ...} =>
              HEADGOAL (embed_tac info cert ctxt))

          val msg =
            Pretty.block
              (Pretty.str "Proved the embedding(s) of " ::
                Pretty.separate "" (map (pretty_const lthy') (map fst consts)))
            |> Pretty.string_of

          val _ = on_thms_complete (fn () => writeln msg) embeds
        in
          (simps @ base_simps, embeds @ base_embeds)
        end

    val (_, embeds) = fold prove_embed code_eqss ([], [])
    val (_, lthy'') = note_thms binding embeds lthy'
  in
    ((rs_term, rs_def, C_info_term, thm), lthy'')
  end

fun method_text_of_tac tac =
  Method.Basic (fn ctxt => fn _ => Method.CONTEXT_TACTIC (tac ctxt))

fun embed_def_cmd def_binding binding raw_consts opts lthy =
  let
    val _ =
      if #cert opts = Skip then
        warning "Skipping certificate proofs"
      else ()

    val (_, lthy') = Local_Theory.open_target lthy
    val def_binding =
      if Binding.is_empty_atts def_binding then
        (Thm.def_binding binding, @{attributes [code]})
      else
        apsnd (fn attribs => @{attributes [code]} @ attribs) def_binding
    val terms = map (Syntax.parse_term lthy') raw_consts
    val ((rs_term, _, C_term, thm), lthy'') = embed_def (binding, def_binding) terms opts lthy'
    val lthy''' = Local_Theory.close_target lthy''
    val phi = Proof_Context.export_morphism lthy'' lthy'''
    val rs_term' = Morphism.term phi rs_term
    val C_term' = Morphism.term phi C_term

    val expr =
      (@{const_name rules}, ((Binding.name_of binding, true), (Expression.Positional [SOME C_term', SOME rs_term'], [])))

    val goal = HOLogic.mk_Trueprop (@{const rules} $ C_term' $ rs_term')

    val meth =
      method_text_of_tac (fn ctxt =>
        case thm of
          SOME thm => HEADGOAL (resolve_tac ctxt [Morphism.thm phi thm])
        | NONE => all_tac)

    val interp =
      if Named_Target.is_theory lthy then
        Interpretation.global_interpretation ([expr], []) []
      else
        Interpretation.sublocale ([expr], []) []

    fun after_qed [[proof]] lthy =
      let
      in
        lthy
        |> interp
        |> Proof.refine_singleton (method_text_of_tac (fn ctxt => HEADGOAL (resolve_tac ctxt [proof])))
        |> Proof.global_immediate_proof
      end
  in
    lthy'''
    |> Proof.theorem NONE after_qed [[(goal, [])]]
    |> Proof.refine_singleton meth
  end

(** setup **)

val parse_flag =
  (Parse.reserved "skip" >> (fn _ => fn {proof, ...} => {cert = Skip, proof = proof}) ||
   Parse.reserved "eval" >> (fn _ => fn {cert, ...} => {cert = cert, proof = Eval}) ||
   Parse.reserved "no_auto" >> (fn _ => fn {cert, ...} => {cert = cert, proof = No_Auto}))

val parse_flags =
  Scan.optional (Args.parens (Parse.list parse_flag >> (fn fs => fold (curry op o) fs I))) I

val _ =
  Outer_Syntax.local_theory_to_proof
    @{command_keyword "embed"}
    "redefines a constant using a deep embedding of term rewriting in HOL"
    ((parse_flags -- Parse_Spec.opt_thm_name ":" -- Parse.binding --| @{keyword "is"} -- Scan.repeat1 Parse.const)
        >> (fn (((opts, def_binding), binding), const) => embed_def_cmd def_binding binding const (opts default_opts)))

end