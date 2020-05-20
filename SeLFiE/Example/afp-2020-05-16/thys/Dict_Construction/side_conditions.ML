signature SIDE_CONDITIONS = sig
  type predicate =
    {f: term,
     index: int,
     inductive: Inductive.result,
     alt: thm option}

  val transform_predicate: morphism -> predicate -> predicate
  val get_predicate: Proof.context -> term -> predicate option
  val set_alt: term -> thm -> Context.generic -> Context.generic
  val is_total: Proof.context -> term -> bool

  val mk_side: thm list -> thm list option -> local_theory -> predicate list * local_theory

  val time_limit: real Config.T
end

structure Side_Conditions : SIDE_CONDITIONS = struct

open Dict_Construction_Util

val time_limit = Attrib.setup_config_real @{binding side_conditions_time_limit} (K 5.0)

val inductive_config =
  {quiet_mode = true, verbose = true, alt_name = Binding.empty, coind = false,
    no_elim = false, no_ind = false, skip_mono = false}

type predicate =
  {f: term,
   index: int,
   inductive: Inductive.result,
   alt: thm option}

fun transform_predicate phi {f, index, inductive, alt} =
  {f = Morphism.term phi f,
   index = index,
   inductive = Inductive.transform_result phi inductive,
   alt = Option.map (Morphism.thm phi) alt}

structure Predicates = Generic_Data
(
  type T = predicate Item_Net.T
  val empty = Item_Net.init (op aconv o apply2 #f) (single o #f)
  val merge = Item_Net.merge
  val extend = I
)

fun get_predicate ctxt t =
  Item_Net.retrieve (Predicates.get (Context.Proof ctxt)) t
  |> try hd
  |> Option.map (transform_predicate (Morphism.transfer_morphism (Proof_Context.theory_of ctxt)))

fun is_total ctxt t =
  let
    val SOME {alt = SOME alt, ...} = get_predicate ctxt t
    val (_, rhs) = Logic.dest_equals (Thm.prop_of alt)
  in rhs = @{term True} end

(* must be of the form [f_side ?x ?y = True] *)
fun set_alt t thm context =
  let
    val thm = safe_mk_meta_eq thm
    val (lhs, _) = Logic.dest_equals (Thm.prop_of thm)
    val {f, index, inductive, ...} = hd (Item_Net.retrieve (Predicates.get context) t)
    val pred = nth (#preds inductive) index
    val (arg_typs, _) = strip_type (fastype_of pred)
    val args =
      Name.invent_names (Variable.names_of (Context.proof_of context)) "x" arg_typs
      |> map Free
    val new_pred = {f = f, index = index, inductive = inductive, alt = SOME thm}
  in
    if Pattern.matches (Context.theory_of context) (lhs, list_comb (pred, args)) then
      Predicates.map (Item_Net.update new_pred) context
    else
      error "Alternative is not fully general"
  end

fun apply_simps ctxt clear thms t =
  let
    val ctxt' =
      Context_Position.not_really ctxt
      |> clear ? put_simpset HOL_ss
  in conv_result (Simplifier.asm_full_rewrite (ctxt' addsimps thms)) t end

fun apply_alts ctxt =
  Item_Net.content (Predicates.get (Context.Proof ctxt))
  |> map #alt
  |> cat_options
  |> apply_simps ctxt true

fun apply_intros ctxt =
  Item_Net.content (Predicates.get (Context.Proof ctxt))
  |> map #inductive
  |> maps #intrs
  |> apply_simps ctxt false

fun dest_head (Free (name, typ)) = (name, typ)
  | dest_head (Const (name, typ)) = (Long_Name.base_name name, typ)

val sideN = "_side"

fun mk_side simps inducts lthy =
  let
    val thy = Proof_Context.theory_of lthy

    val ((_, simps), names) =
      Variable.import true simps lthy
      ||> Variable.names_of

    val (lhss, rhss) =
      map (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) simps
      |> split_list

    val heads = map (`dest_head o (fst o strip_comb)) lhss

    fun mk_typ t = binder_types t ---> @{typ bool}

    val sides = map (apfst (suffix sideN) o apsnd mk_typ o fst) heads

    fun mk_pred_app pred (f, xs) =
      let
        val pred_typs = binder_types (fastype_of pred)
        val exp_param_count = length pred_typs

        val f_typs = take exp_param_count (binder_types (fastype_of f))

        val pred' =
          Envir.subst_term_types (fold (Sign.typ_match thy) (pred_typs ~~ f_typs) Vartab.empty) pred

        val diff = exp_param_count - length xs
      in
        if diff > 0 then
          let
            val bounds = map Bound (0 upto diff - 1)
            val alls = map (K ("x", dummyT)) (0 upto diff - 1)
            val prop = Logic.list_all (alls, HOLogic.mk_Trueprop (list_comb (pred', xs @ bounds)))
          in
            prop (* fishy *)
          end
        else
          HOLogic.mk_Trueprop (list_comb (pred', take exp_param_count xs))
      end

    fun mk_cond f xs =
      if is_Abs f then (* do not look this up in the Item_Net, it'll only end in tears *)
        NONE
      else
        case get_predicate lthy f of
          NONE =>
            (case find_index (equal f o snd) heads of
              ~1 => NONE (* in this case we don't know anything about f; it may be a constructor *)
            | index => SOME (mk_pred_app (Free (nth sides index)) (f, xs)))
        | SOME {index, inductive = {preds, ...}, ...} =>
            SOME (mk_pred_app (nth preds index) (f, xs))

    fun mk_atom f =
      (* in this branch, if f has a non-const-true predicate, it is most likely that there is a
         missing congruence rule *)
      the_list (mk_cond f [])

    fun mk_cong t _ cs =
      let
        val cs' = maps (fn (ctx, ts) => map (Congruences.export_term_ctx ctx) ts) (tl cs)
        val (f, xs) = strip_comb t
        val cs = mk_cond f xs
      in
        the_list cs @ cs'
      end

    val rules = map (Congruences.import_rule lthy) (Function.get_congs lthy)
    val premss =
      map (Congruences.import_term lthy rules) rhss
      |> map (Congruences.fold_tree mk_atom mk_cong)

    val concls =
      map Free sides ~~ map (snd o strip_comb) lhss
      |> map (HOLogic.mk_Trueprop o list_comb)

    val time = Time.fromReal (Config.get lthy time_limit)

    val intros =
      map Logic.list_implies (premss ~~ concls)
      |> Syntax.check_terms lthy
      |> map (apply_alts lthy o Thm.cterm_of lthy)
      |> Par_List.map (with_timeout time (apply_intros lthy o Thm.cterm_of lthy))

    val inds = map (rpair NoSyn o apfst Binding.name) (distinct op = sides)
    val (result, lthy') =
      Inductive.add_inductive inductive_config inds []
        (map (pair (Binding.empty, [])) intros) [] lthy

    fun mk_impartial_goal pred names =
      let
        val param_typs = binder_types (fastype_of pred)
        val (args, names) = fold_map (fn typ => apfst (Free o rpair typ) o Name.variant "x") param_typs names
        val goal = HOLogic.mk_Trueprop (list_comb (pred, args))
      in ((goal, args), names) end

    val ((props, instss), _) =
      fold_map mk_impartial_goal (#preds result) names
      |>> split_list
    val frees = flat instss |> map (fst o dest_Free)

    fun tactic {context = ctxt, ...} =
      let
        val simp_context =
          put_simpset HOL_ss (Context_Position.not_really ctxt) addsimps (#intrs result)
      in
       maybe_induct_tac inducts instss [] ctxt THEN
          PARALLEL_ALLGOALS (Nitpick_Util.DETERM_TIMEOUT time o asm_full_simp_tac simp_context)
      end

    val alts =
      try (Goal.prove_common lthy' NONE frees [] props) tactic
      |> Option.map (map (mk_eq o Thm.close_derivation \<^here>))

    val _ =
      if is_none alts then
        Pretty.str "Potentially underspecified function(s): " ::
          Pretty.commas (map (Syntax.pretty_term lthy o snd) (distinct op = heads))
        |> Pretty.block
        |> Pretty.string_of
        |> warning
      else
        ()

    fun mk_pred n t =
      {f = t, index = n, inductive = result,
       alt = Option.map (fn alts => nth alts n) alts}

    val preds = map_index (fn (n, (_, t)) => mk_pred n t) (distinct op = heads)

    val lthy'' =
      Local_Theory.declaration {pervasive = false, syntax = false}
        (fn phi => fold (Predicates.map o Item_Net.update o transform_predicate phi) preds) lthy'
  in
    (preds, lthy'')
  end

end