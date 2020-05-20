signature CONGRUENCES = sig
  type rule =
    {rule: thm,
     concl: term,
     prems: term list,
     proper: bool}

  type ctx = (string * typ) list * term list
  datatype ctx_tree =
    Tree of (term * (rule * (ctx * ctx_tree) list) option)

  val export_term_ctx: ctx -> term -> term

  val import_rule: Proof.context -> thm -> rule
  val import_term: Proof.context -> rule list -> term -> ctx_tree

  val fold_tree:
    (term -> 'a) ->
    (term -> rule -> (ctx * 'a) list -> 'a) ->
    ctx_tree -> 'a
end

structure Congruences: CONGRUENCES = struct

type rule =
  {rule: thm,
   concl: term,
   prems: term list,
   proper: bool}

type ctx = (string * typ) list * term list

fun export_term_ctx (fixes, assumes) =
  fold_rev (curry Logic.mk_implies) assumes
  #> fold_rev (Logic.all o Free) fixes

datatype ctx_tree =
  Tree of (term * (rule * (ctx * ctx_tree) list) option)

fun fold_tree atom cong t =
  let
    fun go (Tree (t, NONE)) = atom t
      | go (Tree (t, SOME (r, ctxs))) = cong t r (map (apsnd go) ctxs)
  in go t end

fun raw_import_rule {check: bool, proper: bool} ctxt thm =
  let
    val concl = Thm.concl_of thm
    val (lhs, rhs) = Logic.dest_equals concl
    val prems = Thm.prems_of thm
    val rule = {rule = thm, concl = concl, prems = prems, proper = proper}
  in
    if check then
      let
        val ((f_lhs, _), _) = strip_comb lhs |>> dest_Const
        val ((r_lhs, _), _) = strip_comb rhs |>> dest_Const
      in
        if f_lhs <> r_lhs then
          error ("invalid cong rule " ^ Syntax.string_of_term ctxt (Thm.prop_of thm))
        else
          rule
      end
    else
      rule
  end

val import_rule = raw_import_rule {check = true, proper = true}

fun mk_cong n = if n <= 1 then @{thm cong} else mk_cong (n - 1) OF [@{thm cong}]

fun cong_rule n =
  raw_import_rule {check = false, proper = false} @{context} (mk_cong n RS @{thm eq_reflection})

val ext_rule =
  raw_import_rule {check = false, proper = false} @{context} (@{thm ext} RS @{thm eq_reflection})

fun import_term ctxt rules t =
  let
    val thy = Proof_Context.theory_of ctxt

    val lhs_of = fst o HOLogic.dest_eq o HOLogic.dest_Trueprop

    fun go ctxt t =
      let
        (* FIXME eventually, this should be the arity of fst (strip_comb t) *)
        val arity = length (snd (strip_comb t))

        val rules = rules @ [cong_rule arity, ext_rule]

        fun mk_branch subst t =
          let
            val ((params, impl), ctxt') = Variable.focus NONE t ctxt
            val (assms, concl) = Logic.strip_horn impl
            val assms = map (Envir.subst_term subst) assms
          in
            ((map #2 params, assms), (ctxt', lhs_of concl))
          end

        fun match concl =
          try (Pattern.match thy (concl, Logic.mk_equals (t, t))) (Vartab.empty, Vartab.empty)

        fun apply_rule (rule as {concl, prems, ...}) =
          case match concl of
            NONE => NONE
          | SOME subst =>
              SOME (rule, map (mk_branch subst o Envir.beta_norm o Envir.subst_term subst) prems)

        val is_atom = is_Const t orelse is_Free t
      in
        if is_atom then
          Tree (t, NONE)
        else
          case get_first apply_rule rules of
            NONE => error "this shouldn't happen"
          | SOME (rule, branches) => Tree (t, SOME (rule, map (apsnd (uncurry go)) branches))
      end
  in
    go ctxt t
  end

end