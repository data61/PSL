signature LAZY_CASE = sig
  val lazify: Ctr_Sugar.ctr_sugar -> local_theory -> local_theory
  val lazify_typ: typ -> local_theory -> local_theory
  val lazify_cmd: string -> local_theory -> local_theory

  val lazy_case_plugin: string
  val setup: theory -> theory
end

structure Lazy_Case : LAZY_CASE = struct

structure Data = Generic_Data
(
  type T = Symtab.set
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge op =
)

fun init [] = error "empty list"
  | init [_] = []
  | init (x :: xs) = x :: init xs

fun lazify {T, casex, ctrs, case_thms, case_cong, ...} lthy =
  let
    val is_fun = can dest_funT
    val typ_name = fst (dest_Type T)
    val len = length ctrs
    val idxs = 0 upto len - 1

    val (name, typ) = dest_Const casex ||> Logic.unvarifyT_global
    val (typs, _) = strip_type typ

    val exists = Symtab.defined (Data.get (Context.Proof lthy)) typ_name
    val warn = Pretty.separate "" [Syntax.pretty_typ lthy T, Pretty.str "already lazified"]
      |> Pretty.block
    val _ = if exists then warning (Pretty.string_of warn) else ()
  in
    (* for records, casex is the dummy pattern *)
    if Term.is_dummy_pattern casex orelse forall is_fun (init typs) orelse exists then
      lthy
    else
      let
        val arg_typs = init typs

        fun apply_to_unit typ idx =
          if is_fun typ then
            (typ, Bound idx)
          else
            (@{typ unit} --> typ, Bound idx $ @{term "()"})

        val (arg_typs', args) = split_list (map2 apply_to_unit arg_typs (rev idxs))

        val def = list_comb (Const (name, typ), args)
          |> fold_rev Term.abs (map (pair "c") arg_typs')
        val binding = Binding.name "case_lazy"

        val ((term, thm), (lthy', lthy)) =
          Local_Theory.open_target lthy |> snd
          |> Proof_Context.concealed
          |> Local_Theory.map_background_naming (Name_Space.mandatory_path typ_name)
          |> Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), def))
          |>> apsnd snd
          ||> `Local_Theory.close_target
        val phi = Proof_Context.export_morphism lthy lthy'
        val thm' = Morphism.thm phi thm
        val term' = Logic.unvarify_global (Morphism.term phi term)

        fun defs_tac ctxt idx =
          Local_Defs.unfold_tac ctxt [thm', nth case_thms idx] THEN
            HEADGOAL (resolve_tac ctxt @{thms refl})

        val frees = fastype_of term' |> strip_type |> fst |> init
        val frees_f = Name.invent_names Name.context "f0" frees
        val frees_g = Name.invent_names Name.context "g0" frees

        val fs = map Free frees_f
        val gs = map Free frees_g

        fun mk_def_goal ctr idx =
          let
            val (name, len) = dest_Const ctr ||> strip_type ||> fst ||> length
            val frees = Name.invent Name.context "p0" len
            val args = map (Free o rpair dummyT) frees
            val ctr_val = list_comb (Const (name, dummyT), args)
            val lhs = list_comb (term', fs) $ ctr_val
            val rhs =
              if len = 0 then
                nth fs idx $ @{term "()"}
              else
                list_comb (nth fs idx, args)
          in
             (frees, HOLogic.mk_Trueprop (Syntax.check_term lthy' (HOLogic.mk_eq (lhs, rhs))))
          end

        fun prove_defs (frees', goal) idx =
          Goal.prove_future lthy' (map fst frees_f @ frees') [] goal (fn {context, ...} =>
            defs_tac context idx)

        val def_thms = map2 prove_defs (map2 mk_def_goal ctrs idxs) idxs

        val frees = Name.invent_names Name.context "q0" arg_typs
        val unfold_goal =
          let
            val lhs = list_comb (Const (name, typ), map Free frees)
            fun mk_abs (name, typ) =
              if is_fun typ then
                Free (name, typ)
              else
                Abs ("u", @{typ unit}, Free (name, typ))
            val rhs = list_comb (Const (fst (dest_Const term'), dummyT), map mk_abs frees)
          in
            HOLogic.mk_Trueprop (Syntax.check_term lthy' (HOLogic.mk_eq (lhs, rhs)))
          end

        fun unfold_tac ctxt =
          Local_Defs.unfold_tac ctxt [thm'] THEN
            HEADGOAL (resolve_tac ctxt @{thms refl})

        val unfold_thm =
          Goal.prove_future lthy' (map fst frees) [] unfold_goal (fn {context, ...} =>
            unfold_tac context)

        fun mk_cong_prem t ctr (f, g) =
          let
            (* FIXME get rid of dummyT here *)
            fun mk_all t = Logic.all_const dummyT $ Abs ("", dummyT, t)
            val len = dest_Const ctr |> snd |> strip_type |> fst |> length
            val args = map Bound (len - 1 downto 0)
            val ctr_val = list_comb (Logic.unvarify_global ctr, args)
            val args' = if len = 0 then [Bound 0] else args
            val lhs = list_comb (f, args')
            val rhs = list_comb (g, args')
            val concl = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
            val prem = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, ctr_val))
          in fold (K mk_all) args' (Logic.mk_implies (prem, concl)) end

        val cong_goal =
          let
            val t1 = Free ("t1", Logic.unvarifyT_global T)
            val t2 = Free ("t2", Logic.unvarifyT_global T)
            val prems =
              HOLogic.mk_Trueprop (HOLogic.mk_eq (t1, t2)) ::
                map2 (mk_cong_prem t2) ctrs (fs ~~ gs)
            val lhs = list_comb (term', fs) $ t1
            val rhs = list_comb (term', gs) $ t2
            val concl = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
          in
            Logic.list_implies (prems, concl)
            |> Syntax.check_term lthy'
          end

        fun cong_tac ctxt =
          Local_Defs.unfold_tac ctxt [thm'] THEN
            HEADGOAL (eresolve_tac ctxt [case_cong]) THEN
            ALLGOALS (ctxt |> Subgoal.FOCUS
              (fn {context = ctxt, prems, ...} =>
                HEADGOAL (resolve_tac ctxt prems THEN' resolve_tac ctxt prems)))

        val cong_thm =
          Goal.prove_future lthy' ("t1" :: "t2" :: map fst frees_f @ map fst frees_g) [] cong_goal
            (fn {context, ...} => cong_tac context)

        val upd = Data.map (Symtab.update_new (typ_name, ()))
      in
        lthy'
        |> Local_Theory.note ((Binding.empty, @{attributes [code]}), def_thms) |> snd
        |> Local_Theory.note ((Binding.empty, @{attributes [code_unfold]}), [unfold_thm]) |> snd
        |> Local_Theory.note ((Binding.empty, @{attributes [fundef_cong]}), [cong_thm]) |> snd
        |> Local_Theory.declaration {syntax = false, pervasive = true} (K upd)
      end
  end

fun lazify_typ typ lthy =
  lazify (the (Ctr_Sugar.ctr_sugar_of lthy (fst (dest_Type typ)))) lthy

fun lazify_cmd s lthy =
  lazify_typ (Proof_Context.read_type_name {proper = true, strict = false} lthy s) lthy

val lazy_case_plugin =
  Plugin_Name.declare_setup @{binding lazy_case}

(** setup **)

val _ =
  Outer_Syntax.local_theory
    @{command_keyword "lazify"}
    "defines a lazy case constant and sets up the code generator"
    (Scan.repeat1 Args.embedded_inner_syntax >> fold lazify_cmd)

val setup = Ctr_Sugar.ctr_sugar_interpretation lazy_case_plugin (lazify_typ o #T)

end